-- Prove2me | solution 1 for HardyCapset20261020.Cert.case222_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-21T07:17:40.897902+00:00
-- url     : https://prove2.me/submissions/c4dc3255-2134-4d3f-a9dc-8bd84ab13e9b

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate22220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case222_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case222_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate222
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate222.normal = (3190 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate222.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate222.pool = (#[278, 280, 289, 304, 352, 433, 518, 544, 551, 560, 623, 704, 764, 768, 777, 788, 840, 921, 1028, 1032, 1244, 1272, 1492, 1516, 1527, 1536, 1599, 1680, 1734, 1756, 1972, 1974, 2200, 2209, 2272, 2314, 2316, 2353, 2386, 2388, 2438, 2556, 2628, 2678, 2924, 3042, 3114, 3168, 3177, 3190, 3240, 3280, 3289, 3321, 3361, 3370, 3404, 3527, 3553, 3562, 3617, 3634, 3643, 3652, 3894, 4013, 4037, 4046, 4103, 4118, 4127, 4132, 4134, 4253, 4255, 4343, 4345, 4391, 4400, 4463, 4529, 4533, 4544, 4601, 4605, 4624, 4864, 5013, 5085, 5108, 5348, 5352, 5495, 5497, 5585, 5587, 5592, 5713, 5722, 5737, 5794, 5803, 5827, 5836, 5985, 6057, 6076, 6197, 6206, 6223, 6278, 6287, 6313, 6327, 6336, 6380, 6399, 6470, 6479, 6480, 6551, 6560] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate222.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate222.rows = (#[{ vars := #[0, 44, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[3, 49, 106], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[6, 56, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[7, 49, 103], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[12, 40, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[15, 49, 96], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 49, 91], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 49, 90], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[20, 43, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[21, 49, 89], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[22, 64, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[23, 49, 86], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[28, 63, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[29, 49, 85], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 72, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[31, 71, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[49, 51, 55], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[49, 52, 54], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[115, 117, 121], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[115, 118, 120], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[1], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[2], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[4], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[8], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[11], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[27], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[32], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[33], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[35], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[41], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[42], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[46], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[53], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[59], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[70], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[73], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[83], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[97], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[100], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[105], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[108], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[110], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[111], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[113], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[116], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[119], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate222.coverRows = (#[#[0], #[20], #[21], #[1], #[22], #[23], #[2], #[3], #[24], #[25], #[26], #[27], #[4], #[28], #[29], #[5], #[30], #[31], #[6], #[7], #[8], #[9], #[10], #[11], #[32], #[33], #[34], #[35], #[12], #[13], #[14], #[15], #[36], #[37], #[38], #[39], #[40], #[41], #[42], #[43], #[4], #[44], #[45], #[8], #[0], #[46], #[47], #[48], #[49], #[1, 3, 5, 6, 7, 9, 11, 13, 16, 17], #[50], #[16], #[17], #[51], #[17], #[16], #[2], #[52], #[53], #[54], #[55], #[56], #[57], #[12], #[10], #[58], #[59], #[60], #[61], #[62], #[63], #[15], #[14], #[64], #[65], #[66], #[67], #[68], #[69], #[70], #[71], #[72], #[73], #[74], #[75], #[13], #[11], #[76], #[77], #[9], #[7], #[6], #[78], #[79], #[80], #[81], #[5], #[82], #[83], #[84], #[85], #[86], #[87], #[3], #[88], #[89], #[1], #[90], #[91], #[92], #[93], #[94], #[95], #[96], #[97], #[0, 2, 4, 8, 10, 12, 14, 15, 18, 19], #[98], #[18], #[19], #[99], #[19], #[18]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate222 q certificate222.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case222_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case222_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate222.rows.toList.all (rowB certificate222) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate222.pool.size).all (localCoverB certificate222) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate222 < certificate222.denominator * (deletedCount certificate222+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 3190) (0 : ZMod 3) := by
  have hs : certificate222.blockers.size = 6561 := by
    simp only [certificate222, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate222.normal) certificate222.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
