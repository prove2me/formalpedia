-- Prove2me | solution 1 for HardyCapset20261020.Cert.case068_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T19:53:17.375272+00:00
-- url     : https://prove2.me/submissions/9ffb2319-6468-406f-b1e7-909f162b4b12

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate06820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case068_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case068_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate068
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate068.normal = (276 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate068.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate068.pool = (#[276, 277, 278, 285, 294, 307, 308, 316, 317, 357, 379, 380, 438, 460, 461, 523, 524, 532, 533, 543, 544, 545, 552, 561, 595, 596, 624, 676, 677, 705, 761, 768, 777, 791, 798, 807, 840, 870, 921, 951, 1005, 1028, 1244, 1272, 1489, 1497, 1506, 1519, 1527, 1536, 1569, 1599, 1650, 1680, 1734, 1756, 1972, 2001, 2316, 2346, 2388, 2418, 2583, 2655, 2799, 2871, 2927, 2936, 2999, 3080, 3283, 3373, 3550, 3640, 3655, 3664, 3727, 3808, 4013, 4103, 4280, 4370, 4503, 4533, 4575, 4605, 4770, 4842, 4986, 5058, 5114, 5123, 5186, 5267, 5470, 5560, 5737, 5827, 5842, 5851, 5914, 5995, 6200, 6290, 6467, 6557] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate068.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate068.rows = (#[{ vars := #[0, 1, 2], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 3, 4], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 9, 12], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 30, 56], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 40, 54], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 42, 44], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 58, 89], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 60, 88], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 64, 84], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 65, 82], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 70, 103], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 71, 102], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 78, 95], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 79, 94], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 20, 21], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 22, 23], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 26, 29], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 33, 55], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 41, 47], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 43, 57], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 59, 87], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 61, 86], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 62, 85], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 63, 83], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 72, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 73, 104], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 80, 97], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[19, 81, 96], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[6], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[7], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[8], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[11], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[18], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[27], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[31], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[32], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[35], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[46], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[49], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[53], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[100], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate068.coverRows = (#[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], #[0], #[0], #[1], #[1], #[28], #[29], #[30], #[31], #[2], #[32], #[33], #[2], #[34], #[35], #[36], #[37], #[38], #[39], #[14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], #[14], #[14], #[15], #[15], #[40], #[41], #[16], #[42], #[43], #[16], #[3], #[44], #[45], #[17], #[46], #[47], #[48], #[49], #[50], #[51], #[4], #[18], #[5], #[19], #[5], #[52], #[53], #[18], #[54], #[55], #[56], #[57], #[58], #[59], #[4], #[17], #[3], #[19], #[6], #[20], #[7], #[21], #[22], #[23], #[8], #[9], #[60], #[61], #[62], #[63], #[10], #[11], #[24], #[25], #[64], #[65], #[66], #[67], #[12], #[13], #[26], #[27], #[9], #[23], #[8], #[22], #[21], #[20], #[7], #[6], #[68], #[69], #[70], #[71], #[13], #[12], #[27], #[26], #[72], #[73], #[74], #[75], #[11], #[10], #[25], #[24]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate068 q certificate068.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case068_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case068_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate068.rows.toList.all (rowB certificate068) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate068.pool.size).all (localCoverB certificate068) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate068 < certificate068.denominator * (deletedCount certificate068+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 276) (0 : ZMod 3) := by
  have hs : certificate068.blockers.size = 6561 := by
    simp only [certificate068, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate068.normal) certificate068.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
