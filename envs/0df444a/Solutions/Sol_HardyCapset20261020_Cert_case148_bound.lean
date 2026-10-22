-- Prove2me | solution 1 for HardyCapset20261020.Cert.case148_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T22:18:20.428567+00:00
-- url     : https://prove2.me/submissions/a9b81788-c237-4519-af6d-88df8b7d5178

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate14820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case148_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case148_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate148
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate148.normal = (1075 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate148.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate148.pool = (#[289, 316, 349, 352, 379, 422, 524, 551, 589, 662, 677, 704, 777, 804, 833, 840, 867, 908, 1073, 1075, 1077, 1317, 1388, 1500, 1527, 1561, 1636, 1653, 1680, 1801, 1878, 2116, 2118, 2123, 2204, 2209, 2272, 2314, 2316, 2341, 2343, 2357, 2387, 2391, 2414, 2418, 2556, 2583, 2871, 2898, 3042, 3069, 3177, 3240, 3289, 3316, 3526, 3553, 3616, 3643, 3843, 3870, 4010, 4037, 4100, 4127, 4140, 4293, 4337, 4364, 4391, 4396, 4459, 4501, 4503, 4528, 4530, 4544, 4574, 4578, 4601, 4605, 4743, 4770, 5058, 5085, 5229, 5256, 5364, 5427, 5476, 5503, 5713, 5740, 5803, 5830, 6030, 6057, 6197, 6224, 6287, 6314, 6327, 6480, 6524, 6551] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate148.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate148.rows = (#[{ vars := #[0, 16, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[1, 15, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[2, 19, 29], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[3, 13, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[4, 12, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[5, 17, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[6, 19, 28], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[7, 19, 27], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[8, 19, 25], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[9, 22, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[10, 19, 24], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[11, 19, 23], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[14, 19, 21], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 19, 20], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 34, 103], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 41, 102], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 54, 91], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 55, 90], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 66, 77], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 67, 70], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[26, 30, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[31, 32, 33], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 35, 89], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 36, 88], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 52, 72], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 53, 71], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 68, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 69, 104], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[42], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[43], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[46], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[49], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[56], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[59], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[64], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[73], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[83], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[86], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[96], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[97], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[100], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate148.coverRows = (#[#[0], #[1], #[2], #[3], #[4], #[5], #[6], #[7], #[8], #[9], #[10], #[11], #[4], #[3], #[12], #[1], #[0], #[5], #[13], #[2, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], #[13], #[12], #[9], #[11], #[10], #[8], #[20], #[7], #[6], #[2], #[20], #[21], #[21], #[0, 1, 3, 4, 5, 9, 20, 21, 22, 23, 24, 25, 26, 27], #[14], #[22], #[23], #[28], #[29], #[30], #[31], #[15], #[32], #[33], #[34], #[35], #[36], #[37], #[38], #[39], #[40], #[41], #[24], #[25], #[16], #[17], #[42], #[43], #[44], #[45], #[46], #[47], #[48], #[49], #[50], #[51], #[18], #[19], #[26], #[27], #[19], #[25], #[24], #[52], #[53], #[54], #[55], #[18], #[56], #[57], #[58], #[59], #[60], #[61], #[62], #[63], #[64], #[65], #[23], #[22], #[17], #[16], #[66], #[67], #[68], #[69], #[70], #[71], #[72], #[73], #[74], #[75], #[15], #[14], #[27], #[26]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate148 q certificate148.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case148_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case148_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate148.rows.toList.all (rowB certificate148) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate148.pool.size).all (localCoverB certificate148) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate148 < certificate148.denominator * (deletedCount certificate148+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 1075) (0 : ZMod 3) := by
  have hs : certificate148.blockers.size = 6561 := by
    simp only [certificate148, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate148.normal) certificate148.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
