-- Prove2me | solution 1 for HardyCapset20261020.Cert.case144_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T22:09:32.752886+00:00
-- url     : https://prove2.me/submissions/eee9b6d4-b098-4eb7-bb74-685a27f96a6e

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate14420261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case144_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case144_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate144
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate144.normal = (1067 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate144.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate144.pool = (#[96, 183, 281, 308, 341, 353, 380, 423, 427, 430, 532, 559, 576, 581, 584, 670, 676, 703, 761, 767, 768, 788, 794, 795, 827, 833, 839, 840, 866, 867, 905, 1001, 1028, 1067, 1068, 1073, 1145, 1307, 1308, 1311, 1492, 1504, 1509, 1519, 1531, 1536, 1564, 1636, 1642, 1648, 1653, 1675, 1680, 1882, 1884, 1887, 1972, 1999, 2044, 2116, 2127, 2131, 2201, 2212, 2273, 2356, 2921, 2927, 2999, 3161, 3168, 3240, 3281, 3308, 3370, 3397, 3526, 3553, 3652, 3664, 3808, 4100, 4127, 4132, 4149, 4256, 4283, 4293, 4345, 4372, 4388, 4399, 4460, 4543, 5108, 5114, 5186, 5348, 5355, 5427, 5468, 5495, 5557, 5584, 5713, 5740, 5839, 5851, 5995, 6287, 6314, 6319, 6336, 6443, 6470, 6480, 6532, 6559] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate144.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate144.rows = (#[{ vars := #[0, 42], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 107⟩], triples := #[] }, { vars := #[1, 27], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 143⟩], triples := #[] }, { vars := #[4, 39], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 149⟩], triples := #[] }, { vars := #[8, 55], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 118⟩], triples := #[] }, { vars := #[8, 60], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 100⟩], triples := #[] }, { vars := #[12, 114], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 281⟩], triples := #[] }, { vars := #[14, 34], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 149⟩], triples := #[] }, { vars := #[14, 38], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 184⟩], triples := #[] }, { vars := #[23, 54], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 58⟩], triples := #[] }, { vars := #[33, 72, 101], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[33, 73, 100], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[61, 88, 117], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[61, 89, 116], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[6, 20, 61, 7], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 2⟩, ⟨2, 3, 100⟩], triples := #[⟨0, 1, 2⟩] }, { vars := #[2], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[3], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[11], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[18], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[19], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[21], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[30], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[31], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[32], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[35], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[41], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[43], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[46], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[49], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[53], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[56], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[59], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[64], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[70], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[83], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[86], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[96], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[97], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[103], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[105], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[108], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[110], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[111], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[113], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[115], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate144.coverRows = (#[#[0], #[1], #[14], #[15], #[2], #[16], #[13], #[13], #[3, 4], #[17], #[18], #[19], #[5], #[20], #[6, 7], #[21], #[22], #[23], #[24], #[25], #[13], #[26], #[27], #[8], #[28], #[29], #[30], #[1], #[31], #[32], #[33], #[34], #[35], #[9, 10], #[6], #[36], #[37], #[38], #[7], #[2], #[39], #[40], #[0], #[41], #[42], #[43], #[44], #[45], #[46], #[47], #[48], #[49], #[50], #[51], #[8], #[3], #[52], #[53], #[54], #[55], #[4], #[11, 12, 13], #[56], #[57], #[58], #[59], #[60], #[61], #[62], #[63], #[64], #[65], #[9], #[10], #[66], #[67], #[68], #[69], #[70], #[71], #[72], #[73], #[74], #[75], #[76], #[77], #[78], #[79], #[11], #[12], #[80], #[81], #[82], #[83], #[84], #[85], #[86], #[87], #[88], #[89], #[10], #[9], #[90], #[91], #[92], #[93], #[94], #[95], #[96], #[97], #[98], #[99], #[100], #[101], #[5], #[102], #[12], #[11]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate144 q certificate144.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case144_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case144_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate144.rows.toList.all (rowB certificate144) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate144.pool.size).all (localCoverB certificate144) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate144 < certificate144.denominator * (deletedCount certificate144+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 1067) (0 : ZMod 3) := by
  have hs : certificate144.blockers.size = 6561 := by
    simp only [certificate144, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate144.normal) certificate144.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
