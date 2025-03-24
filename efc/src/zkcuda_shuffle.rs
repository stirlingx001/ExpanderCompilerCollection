use crate::attestation::{Attestation, AttestationDataSSZ};
use crate::bls::check_pubkey_key_bls;
use crate::bls_verifier::{convert_point, PairingEntry};
use crate::shuffle::{
    aggregate_attestation_public_key, calculate_balance, flip_with_hash_bits, get_indice_chunk,
    ShuffleJson, MAX_VALIDATOR_EXP, POSEIDON_HASH_LENGTH, SHUFFLE_ROUND, VALIDATOR_CHUNK_SIZE,
};
use crate::utils::{read_from_json_file, sub_vector};
use crate::validator::{ValidatorPlain, ValidatorSSZ};
use ark_std::iterable::Iterable;
use base64::engine::general_purpose::STANDARD;
use base64::Engine;
use circuit_std_rs::gnark::emulated::sw_bls12381::g1::*;
use circuit_std_rs::gnark::emulated::sw_bls12381::g2::*;
use circuit_std_rs::utils::{register_hint, simple_select};
use expander_compiler::frontend::*;
use expander_compiler::zkcuda::context::{call_kernel, Context};
use expander_compiler::zkcuda::kernel::*;
use expander_compiler::zkcuda::proving_system::ExpanderGKRProvingSystem;

#[allow(dead_code)]
fn shuffle_inner<C: Config>(api: &mut API<C>, p: &Vec<Variable>) -> Vec<Variable> {
    println!("len p: {}", p.len());

    let (start_index, pos) = sub_vector(p, 0, 1);
    let (chunk_length, pos) = sub_vector(p, pos, 1);
    let (shuffle_indices, pos) = sub_vector(p, pos, VALIDATOR_CHUNK_SIZE);
    let (_, pos) = sub_vector(p, pos, VALIDATOR_CHUNK_SIZE);
    let (pivots, pos) = sub_vector(p, pos, SHUFFLE_ROUND);
    let (index_count, pos) = sub_vector(p, pos, 1);
    let (position_results, pos) = sub_vector(p, pos, SHUFFLE_ROUND * VALIDATOR_CHUNK_SIZE);
    let (position_bit_results, pos) = sub_vector(p, pos, SHUFFLE_ROUND * VALIDATOR_CHUNK_SIZE);
    let (flip_results, pos) = sub_vector(p, pos, SHUFFLE_ROUND * VALIDATOR_CHUNK_SIZE);

    let (slot, pos) = sub_vector(p, pos, 8);
    let (committee_index, pos) = sub_vector(p, pos, 8);
    let (beacon_beacon_block_root, pos) = sub_vector(p, pos, 32);
    let (source_epoch, pos) = sub_vector(p, pos, 8);
    let (target_epoch, pos) = sub_vector(p, pos, 8);
    let (source_root, pos) = sub_vector(p, pos, 32);
    let (target_root, pos) = sub_vector(p, pos, 32);

    let (attestation_hm, pos) = sub_vector(p, pos, 48 * 2 * 2);

    let (attestation_sig_bytes, pos) = sub_vector(p, pos, 96);
    let (attestation_sig_g2, pos) = sub_vector(p, pos, 48 * 2 * 2);
    let (aggregation_bits, pos) = sub_vector(p, pos, VALIDATOR_CHUNK_SIZE);
    let (validator_hashes, pos) = sub_vector(p, pos, POSEIDON_HASH_LENGTH * VALIDATOR_CHUNK_SIZE);
    let (aggregated_pubkey, pos) = sub_vector(p, pos, 48 * 2);
    let (attestation_balance, pos) = sub_vector(p, pos, 8);
    let (pubkeys_bls, pos) = sub_vector(p, pos, 48 * 2 * VALIDATOR_CHUNK_SIZE);
    let (pubkey, pos) = sub_vector(p, pos, 48 * VALIDATOR_CHUNK_SIZE);
    let (withdrawal_credentials, pos) = sub_vector(p, pos, 32 * VALIDATOR_CHUNK_SIZE);
    let (effective_balance, pos) = sub_vector(p, pos, 8 * VALIDATOR_CHUNK_SIZE);
    let (slashed, pos) = sub_vector(p, pos, VALIDATOR_CHUNK_SIZE);
    let (activation_eligibility_epoch, pos) = sub_vector(p, pos, 8 * VALIDATOR_CHUNK_SIZE);
    let (activation_epoch, pos) = sub_vector(p, pos, 8 * VALIDATOR_CHUNK_SIZE);
    let (exit_epoch, pos) = sub_vector(p, pos, 8 * VALIDATOR_CHUNK_SIZE);
    let (withdrawable_epoch, _) = sub_vector(p, pos, 8 * VALIDATOR_CHUNK_SIZE);

    //println!("pos: {}", pos);
    //api.assert_is_equal(p[0], 1);
    //return vec![api.constant(1)];

    let mut g1 = G1::new(api);
    let mut indices_chunk =
        get_indice_chunk(api, start_index[0], chunk_length[0], VALIDATOR_CHUNK_SIZE);

    //set padding indices to 0
    let zero_var = api.constant(0);
    for (i, chunk) in indices_chunk.iter_mut().enumerate() {
        let tmp = api.add(flip_results[i], 1);
        let ignore_flag = api.is_zero(tmp);
        *chunk = simple_select(api, ignore_flag, zero_var, *chunk);
    }

    //flip the indices based on the hashbit
    let mut copy_cur_indices = indices_chunk.clone();
    for i in 0..SHUFFLE_ROUND {
        let (cur_indices, diffs) = flip_with_hash_bits(
            api,
            pivots[i],
            index_count[0],
            &copy_cur_indices,
            &position_results[i * VALIDATOR_CHUNK_SIZE..(i + 1) * VALIDATOR_CHUNK_SIZE],
            &position_bit_results[i * VALIDATOR_CHUNK_SIZE..(i + 1) * VALIDATOR_CHUNK_SIZE],
            &flip_results[i * VALIDATOR_CHUNK_SIZE..(i + 1) * VALIDATOR_CHUNK_SIZE],
        );
        for diff in diffs {
            g1.curve_f.table.rangeproof(api, diff, MAX_VALIDATOR_EXP);
        }
        copy_cur_indices = api.new_hint("myhint.copyvarshint", &cur_indices, cur_indices.len());
    }
    //check the final curIndices, should be equal to the shuffleIndex
    for (i, cur_index) in copy_cur_indices
        .iter_mut()
        .enumerate()
        .take(shuffle_indices.len())
    {
        let tmp = api.add(flip_results[i], 1);
        let is_minus_one = api.is_zero(tmp);
        *cur_index = simple_select(api, is_minus_one, shuffle_indices[i], *cur_index);
        let tmp = api.sub(shuffle_indices[i], *cur_index);
        let tmp_res = api.is_zero(tmp);
        api.assert_is_equal(tmp_res, 1);
    }

    let mut pubkey_list = vec![];
    let mut acc_balance = vec![];
    for i in 0..VALIDATOR_CHUNK_SIZE {
        let mut pubkey_tmp: [Variable; 48] = [Variable::default(); 48];
        let mut effective_balance_tmp = [Variable::default(); 8];
        for j in 0..48 {
            pubkey_tmp[j] = pubkey[i * 48 + j];
        }
        for j in 0..8 {
            effective_balance_tmp[j] = effective_balance[i * 8 + j];
        }
        pubkey_list.push(pubkey_tmp);
        acc_balance.push(effective_balance_tmp);
    }
    let effect_balance = calculate_balance(api, &mut acc_balance, &aggregation_bits);
    for (i, cur_effect_balance) in effect_balance.iter().enumerate() {
        api.assert_is_equal(cur_effect_balance, attestation_balance[i]);
    }

    let mut pubkey_list_bls = vec![];
    for (i, cur_pubkey) in pubkey_list.iter().enumerate() {
        let pubkey_g1 = G1Affine::from_vars(
            pubkeys_bls[i * 96..i * 96 + 48].to_vec(),
            pubkeys_bls[i * 96 + 48..i * 96 + 96].to_vec(),
        );
        let logup_var = check_pubkey_key_bls(api, cur_pubkey.to_vec(), &pubkey_g1);
        g1.curve_f.table.rangeproof(api, logup_var, 5);
        pubkey_list_bls.push(pubkey_g1);
    }

    let mut aggregated_pubkey = G1Affine::from_vars(
        aggregated_pubkey[0..48].to_vec(),
        aggregated_pubkey[48..].to_vec(),
    );
    aggregate_attestation_public_key(
        api,
        &mut g1,
        &pubkey_list_bls,
        &aggregation_bits,
        &mut aggregated_pubkey,
    );

    for index in 0..VALIDATOR_CHUNK_SIZE {
        let mut validator = ValidatorSSZ::new();
        for i in 0..48 {
            validator.public_key[i] = pubkey[index * 48 + i];
        }
        for i in 0..32 {
            validator.withdrawal_credentials[i] = withdrawal_credentials[index * 32 + i];
        }
        for i in 0..8 {
            validator.effective_balance[i] = effective_balance[index * 8 + i];
        }
        for i in 0..1 {
            validator.slashed[i] = slashed[index * 1 + i];
        }
        for i in 0..8 {
            validator.activation_eligibility_epoch[i] = activation_eligibility_epoch[index * 8 + i];
        }
        for i in 0..8 {
            validator.activation_epoch[i] = activation_epoch[index * 8 + i];
        }
        for i in 0..8 {
            validator.exit_epoch[i] = exit_epoch[index * 8 + i];
        }
        for i in 0..8 {
            validator.withdrawable_epoch[i] = withdrawable_epoch[index * 8 + i];
        }
        let hash = validator.hash(api);
        for (i, hashbit) in hash.iter().enumerate().take(8) {
            api.assert_is_equal(hashbit, validator_hashes[index * 8 + i]);
        }
    }
    // attestation
    let att_ssz = AttestationDataSSZ {
        slot: slot.try_into().expect("Expected a Vec of length 8"),
        committee_index: committee_index
            .try_into()
            .expect("Expected a Vec of length 8"),
        beacon_block_root: beacon_beacon_block_root
            .try_into()
            .expect("Expected a Vec of length 32"),
        source_epoch: source_epoch.try_into().expect("Expected a Vec of length 8"),
        target_epoch: target_epoch.try_into().expect("Expected a Vec of length 8"),
        source_root: source_root.try_into().expect("Expected a Vec of length 32"),
        target_root: target_root.try_into().expect("Expected a Vec of length 32"),
    };
    let mut g2 = G2::new(api);
    // domain
    let domain = [
        1, 0, 0, 0, 187, 164, 218, 150, 53, 76, 159, 37, 71, 108, 241, 188, 105, 191, 88, 58, 127,
        158, 10, 240, 73, 48, 91, 98, 222, 103, 102, 64,
    ];
    let mut domain_var = vec![];
    for domain_byte in domain.iter() {
        domain_var.push(api.constant(domain_byte as u32));
    }
    let att_hash = att_ssz.att_data_signing_root(api, &domain_var); //msg
                                                                    //map to hm
    let (hm0, hm1) = g2.hash_to_fp(api, &att_hash);
    let hm_g2 = g2.map_to_g2(api, &hm0, &hm1);
    let expected_hm_g2 = G2AffP::from_vars(
        attestation_hm[..48].to_vec(),
        attestation_hm[48..96].to_vec(),
        attestation_hm[96..144].to_vec(),
        attestation_hm[144..].to_vec(),
    );
    g2.assert_is_equal(api, &hm_g2, &expected_hm_g2);
    // unmarshal attestation sig
    let sig_g2 = g2.uncompressed(api, &attestation_sig_bytes);
    let expected_sig_g2 = G2AffP::from_vars(
        attestation_sig_g2[..48].to_vec(),
        attestation_sig_g2[48..96].to_vec(),
        attestation_sig_g2[96..144].to_vec(),
        attestation_sig_g2[144..].to_vec(),
    );
    g2.assert_is_equal(api, &sig_g2, &expected_sig_g2);
    g2.ext2.curve_f.check_mul(api);
    g2.ext2.curve_f.table.final_check(api);
    g2.ext2.curve_f.table.final_check(api);
    g2.ext2.curve_f.table.final_check(api);

    g1.curve_f.check_mul(api);
    g1.curve_f.table.final_check(api);
    g1.curve_f.table.final_check(api);
    g1.curve_f.table.final_check(api);

    return vec![api.constant(1)];
}

#[kernel]
fn compute_shuffle<C: Config>(
    api: &mut API<C>,
    input: &[InputVariable; 255781],
    output: &mut OutputVariable,
) {
    let outc = api.memorized_simple_call(shuffle_inner, input);
    *output = outc[0]
}

fn assign_input(dir: &str) -> Vec<M31> {
    //let plain_validators = read_validators(dir);
    let file_path = format!("{}/validatorList.json", dir);
    let plain_validators: Vec<ValidatorPlain> = read_from_json_file(&file_path).unwrap();
    let file_path = format!("{}/shuffle_assignment.json", dir);
    let shuffle_datas: Vec<ShuffleJson> = read_from_json_file(&file_path).unwrap();
    let file_path = format!("{}/pubkeyBLSList.json", dir);
    let public_key_bls: Vec<Vec<String>> = read_from_json_file(&file_path).unwrap();
    let file_path = format!("{}/slotAttestationsFolded.json", dir);
    let attestations: Vec<Attestation> = read_from_json_file(&file_path).unwrap();
    let file_path = format!("{}/pairing_assignment.json", dir);
    let pairing_datas: Vec<PairingEntry> = read_from_json_file(&file_path).unwrap();

    let shuffle_data = shuffle_datas[0].clone();
    let attestation = attestations[0].clone();
    let pairing_entry = pairing_datas[0].clone();

    let mut p = vec![];
    p.push(M31::from(shuffle_data.start_index));
    p.push(M31::from(shuffle_data.chunk_length));
    for i in 0..VALIDATOR_CHUNK_SIZE {
        p.push(M31::from(shuffle_data.shuffle_indices[i]));
    }
    for i in 0..VALIDATOR_CHUNK_SIZE {
        p.push(M31::from(shuffle_data.committee_indices[i]));
    }
    for i in 0..SHUFFLE_ROUND {
        p.push(M31::from(shuffle_data.pivots[i]));
    }
    p.push(M31::from(shuffle_data.index_count));

    for i in 0..SHUFFLE_ROUND * VALIDATOR_CHUNK_SIZE {
        p.push(M31::from(shuffle_data.position_results[i]));
    }

    for i in 0..SHUFFLE_ROUND * VALIDATOR_CHUNK_SIZE {
        p.push(M31::from(shuffle_data.position_bit_results[i]));
    }
    for i in 0..SHUFFLE_ROUND * VALIDATOR_CHUNK_SIZE {
        p.push(M31::from(shuffle_data.flip_results[i]));
    }

    //attestationdata

    let slot = attestation.data.slot.to_le_bytes();
    for (_, slot_byte) in slot.iter().enumerate() {
        p.push(M31::from(slot_byte as u32));
    }
    let committee_index = attestation.data.committee_index.to_le_bytes();
    for (_, committee_index_byte) in committee_index.iter().enumerate() {
        p.push(M31::from(committee_index_byte as u32));
    }

    let beacon_beacon_block_root = attestation.data.beacon_block_root.clone();
    let beacon_beacon_block_root = STANDARD.decode(beacon_beacon_block_root).unwrap();
    for (_, beacon_beacon_block_root_byte) in beacon_beacon_block_root.iter().enumerate() {
        p.push(M31::from(*beacon_beacon_block_root_byte as u32));
    }

    //assign source_epoch
    let source_epoch = attestation.data.source.epoch.to_le_bytes();
    for (j, source_epoch_byte) in source_epoch.iter().enumerate() {
        p.push(M31::from(source_epoch_byte as u32));
    }
    //assign target_epoch
    let target_epoch = attestation.data.target.epoch.to_le_bytes();
    for (j, target_epoch_byte) in target_epoch.iter().enumerate() {
        p.push(M31::from(target_epoch_byte as u32));
    }

    //assign source_root
    let source_root = attestation.data.source.root.clone();
    let source_root = STANDARD.decode(source_root).unwrap();
    for (_, source_root_byte) in source_root.iter().enumerate() {
        p.push(M31::from(*source_root_byte as u32));
    }
    //assign target_root
    let target_root = attestation.data.target.root.clone();
    let target_root = STANDARD.decode(target_root).unwrap();
    for (_, target_root_byte) in target_root.iter().enumerate() {
        p.push(M31::from(*target_root_byte as u32));
    }

    let attestation_hm0 = convert_point(pairing_entry.hm.p.x.clone());
    let attestation_hm1 = convert_point(pairing_entry.hm.p.y.clone());
    for i in 0..2 {
        for j in 0..48 {
            p.push(attestation_hm0[i][j])
        }
    }
    for i in 0..2 {
        for j in 0..48 {
            p.push(attestation_hm1[i][j])
        }
    }

    //assign attestation_sig_bytes
    let attestation_sig_bytes = attestation.signature.clone();
    let attestation_sig_bytes = STANDARD.decode(attestation_sig_bytes).unwrap();
    for (j, attestation_sig_byte) in attestation_sig_bytes.iter().enumerate() {
        p.push(M31::from(*attestation_sig_byte as u32));
    }
    //assign attestation_sig_g2
    let attestation_sig_g20 = convert_point(pairing_entry.signature.p.x.clone());
    let attestation_sig_g21 = convert_point(pairing_entry.signature.p.y.clone());

    for i in 0..2 {
        for j in 0..48 {
            p.push(attestation_sig_g20[i][j])
        }
    }
    for i in 0..2 {
        for j in 0..48 {
            p.push(attestation_sig_g21[i][j])
        }
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        p.push(M31::from(shuffle_data.aggregation_bits[i]));
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        for j in 0..POSEIDON_HASH_LENGTH {
            p.push(M31::from(shuffle_data.validator_hashes[i][j]));
        }
    }

    let pubkey = &shuffle_data.aggregated_pubkey;
    for i in 0..48 {
        p.push(M31::from(pubkey.x.limbs[i] as u32))
    }
    for i in 0..48 {
        p.push(M31::from(pubkey.y.limbs[i] as u32))
    }


    for i in 0..8 {
        p.push(M31::from(shuffle_data.attestation_balance[i]));
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let raw_pubkey_bls = &public_key_bls[shuffle_data.committee_indices[i] as usize];
        let pubkey_bls_x = STANDARD.decode(&raw_pubkey_bls[0]).unwrap();
        let pubkey_bls_y = STANDARD.decode(&raw_pubkey_bls[1]).unwrap();
        for k in 0..48 {
            p.push(M31::from(pubkey_bls_x[47 - k] as u32));
        }
        for k in 0..48 {
            p.push(M31::from(pubkey_bls_y[47 - k] as u32));
        }
    }
    for i in 0..VALIDATOR_CHUNK_SIZE {
        //assign validator
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let raw_pubkey = validator.public_key.clone();
        let pubkey = STANDARD.decode(raw_pubkey).unwrap();
        for (_, pubkey_byte) in pubkey.iter().enumerate().take(48) {
            p.push(M31::from(*pubkey_byte as u32));
        }
    }
    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let raw_withdrawal_credentials = validator.withdrawal_credentials.clone();
        let withdrawal_credentials = STANDARD.decode(raw_withdrawal_credentials).unwrap();
        for (_, withdrawal_credentials_byte) in withdrawal_credentials.iter().enumerate().take(32) {
            p.push(M31::from(*withdrawal_credentials_byte as u32));
        }
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let effective_balance = validator.effective_balance.to_le_bytes();
        for (_, effective_balance_byte) in effective_balance.iter().enumerate() {
            p.push(M31::from(effective_balance_byte as u32));
        }
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let slashed = if validator.slashed { 1 } else { 0 };
        p.push(M31::from(slashed));
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let activation_eligibility_epoch = validator.activation_eligibility_epoch.to_le_bytes();
        for (_, activation_eligibility_epoch_byte) in
            activation_eligibility_epoch.iter().enumerate()
        {
            p.push(M31::from(activation_eligibility_epoch_byte as u32));
        }
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let activation_epoch = validator.activation_epoch.to_le_bytes();
        for (_, activation_epoch_byte) in activation_epoch.iter().enumerate() {
            p.push(M31::from(activation_epoch_byte as u32));
        }
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let exit_epoch = validator.exit_epoch.to_le_bytes();
        for (_, exit_epoch_byte) in exit_epoch.iter().enumerate() {
           p.push(M31::from(exit_epoch_byte as u32));
        }
    }

    for i in 0..VALIDATOR_CHUNK_SIZE {
        let validator = plain_validators[shuffle_data.committee_indices[i] as usize].clone();
        let withdrawable_epoch = validator.withdrawable_epoch.to_le_bytes();
        for (_, withdrawable_epoch_byte) in withdrawable_epoch.iter().enumerate() {
           p.push( M31::from(withdrawable_epoch_byte as u32));
        }
    }
    p
}

//#[test]
pub fn test_zkcuda_shuffle() {

    let p = assign_input(".");
    println!("prepare data ok");

    let mut hint_registry1 = HintRegistry::<M31>::new();
    register_hint(&mut hint_registry1);

    let mut ctx: Context<M31Config, ExpanderGKRProvingSystem<M31Config>, _> =
        Context::new(hint_registry1);

    let p = ctx.copy_to_device(&vec![p], false);

    println!("copy to device ok");

    let start_time = std::time::Instant::now();
    let kernel: Kernel<M31Config> =  compile_compute_shuffle().unwrap();

    let t2 = std::time::Instant::now();
    println!("compile ok, time {:?}", t2.duration_since(start_time));

    let mut out = None;
    call_kernel!(ctx, kernel, p, mut out);
    let t3 = std::time::Instant::now();
    println!("call kernel ok, time {:?}", t3.duration_since(t2));

    let computation_graph = ctx.to_computation_graph();

    let proof = ctx.to_proof();

    assert!(computation_graph.verify(&proof));

    let t4 = std::time::Instant::now();

    println!("verify ok, time {:?}", t4.duration_since(t3));
}