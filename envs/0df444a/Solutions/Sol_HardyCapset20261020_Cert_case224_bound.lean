-- Prove2me | solution 1 for HardyCapset20261020.Cert.case224_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-21T07:19:57.519672+00:00
-- url     : https://prove2.me/submissions/0736f6dc-1786-4ed9-9057-75ebb5904d19

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate22420261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case224_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case224_blockers1
import Theorems.Thm_HardyCapset20261020_Cert_boolean_check_completion_bound
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option autoImplicit false
namespace HardyCapset20261020.Cert
private theorem range_list_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

@[cbv_eval] theorem dotCode_list (n q : ℕ) :
    dotCode n q = (((List.range 8).map (fun i => digit n i * digit q i)).sum % 3) := by
  unfold dotCode natDot
  rw [range_list_sum, ← Fin.sum_univ_eq_sum_range]

@[cbv_eval] theorem coefficient_list (r : Row) (j : ℕ) :
    coefficient r j = ((List.range r.vars.size).map
      (fun k => if entry r.vars k = j then entry r.coeff k else 0)).sum := by
  unfold coefficient
  rw [range_list_sum, ← Fin.sum_univ_eq_sum_range]

@[cbv_eval] theorem cost_list (c : Certificate) :
    cost c = ((List.range c.rows.size).map
      (fun k => c.rows[k]!.weight * c.rows[k]!.bound)).sum := by
  unfold cost
  rw [range_list_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [k.isLt]
end HardyCapset20261020.Cert
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
-- Keep arithmetic operations intact until their arguments are values. The
-- built-in literal evaluators then return kernel-checked equality proofs.
attribute [cbv_opaque] Nat.add Nat.mul Nat.sub Nat.ble
namespace HardyCapset20261020.Cert
@[cbv_eval] theorem decide_le_nat (a b : Nat) : decide (a ≤ b) = a.ble b := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Nat.ble_eq]
@[cbv_eval] theorem decide_lt_nat (a b : Nat) : decide (a < b) = a.succ.ble b := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Nat.ble_eq, Nat.succ_le_iff]
end HardyCapset20261020.Cert
namespace HardyCapset20261020.Cert
private theorem evaluation_base_size : baseArray.size = 512 := by decide_cbv
attribute [cbv_eval] fast_baseline_lookup evaluation_base_size
attribute [cbv_opaque] baseArray
end HardyCapset20261020.Cert
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate224
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate224.normal = (3191 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate224.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate224.pool = (#[277, 281, 290, 305, 353, 434, 517, 545, 550, 559, 622, 703, 767, 768, 776, 777, 791, 824, 833, 839, 840, 905, 914, 920, 921, 1032, 1064, 1073, 1145, 1154, 1271, 1272, 1489, 1522, 1527, 1531, 1536, 1555, 1564, 1594, 1599, 1636, 1645, 1675, 1680, 1729, 1734, 1974, 2035, 2044, 2116, 2125, 2201, 2210, 2273, 2315, 2316, 2354, 2387, 2388, 2437, 2556, 2628, 2677, 2927, 2936, 2999, 3042, 3080, 3114, 3168, 3177, 3191, 3240, 3281, 3310, 3321, 3371, 3400, 3526, 3535, 3550, 3554, 3607, 3616, 3640, 3644, 3649, 3889, 3894, 4036, 4040, 4126, 4130, 4134, 4256, 4265, 4280, 4337, 4346, 4370, 4390, 4399, 4462, 4528, 4533, 4543, 4600, 4605, 4625, 4865, 5013, 5085, 5111, 5352, 5470, 5494, 5503, 5560, 5575, 5584, 5591, 5592, 5710, 5714, 5800, 5804, 5842, 5851, 5914, 5985, 5995, 6057, 6196, 6200, 6224, 6233, 6286, 6290, 6305, 6314, 6327, 6336, 6379, 6399, 6440, 6469, 6480, 6530, 6559] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate224.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate224.rows = (#[{ vars := #[16, 72, 121], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 62, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[21, 61, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[27, 59, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[28, 56, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 72, 113], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[32, 88, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[38, 72, 112], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[41, 72, 111], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[45, 87, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[49, 72, 108], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[50, 72, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[55, 72, 98], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[58, 72, 96], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[67, 72, 83], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[69, 72, 80], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[72, 74, 77], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[104, 119, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[107, 117, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[130, 139, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[132, 136, 143], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[143, 146, 149], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[1], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[2], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[3], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[4], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[6], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[7], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[8], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[11], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[12], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[19], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[20], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[23], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[31], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[33], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[35], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[42], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[43], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[46], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[53], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[54], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[64], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[70], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[73], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[86], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[89], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[97], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[100], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[103], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[110], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[115], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[116], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[118], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[120], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[122], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[123], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[124], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[125], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[126], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[127], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[128], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[129], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[131], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[133], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[134], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[135], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[137], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[138], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[140], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[141], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[142], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[144], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[145], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[147], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[148], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate224.coverRows = (#[#[22], #[23], #[24], #[25], #[26], #[27], #[28], #[29], #[30], #[31], #[32], #[33], #[34], #[35], #[36], #[37], #[0], #[38], #[1], #[39], #[40], #[2], #[41], #[42], #[43], #[44], #[45], #[3], #[4], #[46], #[5], #[47], #[6], #[48], #[49], #[50], #[51], #[52], #[7], #[53], #[54], #[8], #[55], #[56], #[57], #[9], #[58], #[59], #[60], #[10], #[11], #[61], #[62], #[63], #[64], #[12], #[4], #[65], #[13], #[3], #[66], #[2], #[1], #[67], #[68], #[69], #[70], #[14], #[71], #[15], #[72], #[73], #[0, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16], #[74], #[16], #[75], #[76], #[16], #[77], #[78], #[15], #[79], #[80], #[14], #[81], #[82], #[83], #[9], #[6], #[84], #[85], #[86], #[87], #[88], #[89], #[90], #[13], #[91], #[12], #[92], #[93], #[94], #[95], #[96], #[17], #[11], #[97], #[18], #[10], #[98], #[99], #[8], #[7], #[5], #[100], #[101], #[102], #[18], #[103], #[17], #[104], #[0], #[105], #[106], #[107], #[108], #[109], #[110], #[111], #[112], #[19], #[113], #[20], #[114], #[115], #[116], #[20], #[117], #[118], #[19], #[119], #[120], #[121], #[1, 2, 3, 4, 6, 9, 17, 18, 19, 20, 21], #[122], #[123], #[21], #[124], #[125], #[21]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate224 q certificate224.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case224_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case224_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate224.rows.toList.all (rowB certificate224) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate224.pool.size).all (localCoverB certificate224) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate224 < certificate224.denominator * (deletedCount certificate224+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 3191) (0 : ZMod 3) := by
  have hs : certificate224.blockers.size = 6561 := by
    simp only [certificate224, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate224.normal) certificate224.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
