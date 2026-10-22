-- Prove2me | solution 1 for HardyCapset20261020.Cert.case052_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T19:25:44.659173+00:00
-- url     : https://prove2.me/submissions/34d86c82-01eb-46d1-8481-32e80c33cafd

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate05220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case052_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case052_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate052
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate052.normal = (250 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate052.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate052.pool = (#[250, 277, 281, 290, 304, 308, 317, 340, 349, 353, 380, 421, 430, 434, 461, 491, 518, 523, 532, 545, 550, 559, 581, 590, 595, 622, 662, 671, 676, 703, 737, 764, 791, 827, 836, 908, 917, 974, 1001, 1028, 1064, 1073, 1145, 1154, 1462, 1489, 1516, 1552, 1561, 1633, 1642, 1945, 1972, 1999, 2035, 2044, 2116, 2125, 2200, 2204, 2209, 2213, 2272, 2276, 2353, 2357, 2437, 2678, 2924, 3042, 3069, 3114, 3141, 3161, 3283, 3310, 3373, 3400, 3649, 3771, 3798, 3843, 3870, 4132, 4253, 4280, 4343, 4370, 4387, 4391, 4396, 4400, 4459, 4463, 4540, 4544, 4624, 4865, 5111, 5229, 5256, 5301, 5328, 5348, 5470, 5497, 5560, 5587, 5836, 5958, 5985, 6030, 6057, 6319, 6440, 6467, 6530, 6557] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate052.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate052.rows = (#[{ vars := #[0, 1, 4], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 7, 12], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 8, 11], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 66, 96], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[15, 16, 19], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[15, 22, 27], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[15, 23, 26], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[15, 67, 97], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 31, 32], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 33, 36], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 34, 35], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 68, 98], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[37, 38, 39], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[37, 40, 43], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[37, 41, 42], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[37, 73, 103], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[44, 45, 46], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[44, 47, 50], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[44, 48, 49], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[44, 78, 108], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[51, 52, 53], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[51, 54, 57], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[51, 55, 56], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[51, 83, 113], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[2], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[3], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[6], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[18], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[20], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[21], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[59], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[64], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[70], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[72], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[86], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[89], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[100], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[105], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[110], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[111], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[115], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[116], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[117], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate052.coverRows = (#[#[0, 1, 2, 3], #[0], #[24], #[25], #[0], #[26], #[27], #[1], #[2], #[28], #[29], #[2], #[1], #[30], #[31], #[4, 5, 6, 7], #[4], #[32], #[33], #[4], #[34], #[35], #[5], #[6], #[36], #[37], #[6], #[5], #[38], #[39], #[8, 9, 10, 11], #[8], #[8], #[9], #[10], #[10], #[9], #[12, 13, 14, 15], #[12], #[12], #[13], #[14], #[14], #[13], #[16, 17, 18, 19], #[16], #[16], #[17], #[18], #[18], #[17], #[20, 21, 22, 23], #[20], #[20], #[21], #[22], #[22], #[21], #[40], #[41], #[42], #[43], #[44], #[45], #[46], #[47], #[3], #[7], #[11], #[48], #[49], #[50], #[51], #[15], #[52], #[53], #[54], #[55], #[19], #[56], #[57], #[58], #[59], #[23], #[60], #[61], #[62], #[63], #[64], #[65], #[66], #[67], #[68], #[69], #[70], #[71], #[3], #[7], #[11], #[72], #[73], #[74], #[75], #[15], #[76], #[77], #[78], #[79], #[19], #[80], #[81], #[82], #[83], #[23], #[84], #[85], #[86], #[87]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate052 q certificate052.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case052_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case052_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate052.rows.toList.all (rowB certificate052) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate052.pool.size).all (localCoverB certificate052) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate052 < certificate052.denominator * (deletedCount certificate052+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 250) (0 : ZMod 3) := by
  have hs : certificate052.blockers.size = 6561 := by
    simp only [certificate052, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate052.normal) certificate052.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
