-- Prove2me | solution 1 for HardyCapset20261020.Cert.case030_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T18:45:06.433292+00:00
-- url     : https://prove2.me/submissions/d9e06e6b-4c24-4de6-954d-d04868d34902

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate03020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case030_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case030_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate030
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate030.normal = (100 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate030.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate030.pool = (#[100, 173, 280, 290, 307, 317, 347, 349, 353, 380, 418, 422, 433, 460, 523, 533, 550, 560, 589, 593, 596, 623, 662, 664, 676, 703, 776, 803, 839, 866, 905, 908, 1005, 1032, 1068, 1145, 1150, 1158, 1245, 1272, 1308, 1388, 1390, 1398, 1495, 1522, 1561, 1564, 1648, 1675, 1734, 1761, 1797, 1801, 1808, 1887, 1974, 2001, 2037, 2044, 2048, 2127, 2200, 2203, 2210, 2213, 2273, 2276, 2314, 2341, 2353, 2356, 2387, 2414, 2936, 2999, 3165, 3289, 3316, 3405, 3535, 3562, 3655, 3808, 3894, 4091, 4118, 4134, 4337, 4364, 4387, 4390, 4397, 4400, 4460, 4463, 4501, 4528, 4540, 4543, 4574, 4601, 5123, 5186, 5352, 5476, 5503, 5592, 5722, 5749, 5842, 5995, 6081, 6278, 6305, 6321, 6524, 6551] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate030.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate030.rows = (#[{ vars := #[6, 46], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 127⟩], triples := #[] }, { vars := #[6, 53], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 115⟩], triples := #[] }, { vars := #[10, 30], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 189⟩], triples := #[] }, { vars := #[10, 35], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 177⟩], triples := #[] }, { vars := #[19, 47], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 115⟩], triples := #[] }, { vars := #[19, 59], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 127⟩], triples := #[] }, { vars := #[23, 31], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 177⟩], triples := #[] }, { vars := #[23, 41], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 189⟩], triples := #[] }, { vars := #[36, 64], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 494⟩], triples := #[] }, { vars := #[60, 108], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 240⟩], triples := #[] }, { vars := #[0, 68, 97], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 69, 96], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[1, 72, 101], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[1, 73, 100], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0, 12, 16, 54], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 127⟩, ⟨2, 3, 103⟩], triples := #[⟨0, 1, 2⟩] }, { vars := #[1, 3, 21, 42], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 177⟩, ⟨1, 3, 157⟩], triples := #[⟨0, 1, 2⟩] }, { vars := #[2], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[4], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[7], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[8], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[11], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[18], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[20], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[27], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[32], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[33], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[43], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[49], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[55], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[56], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[70], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[83], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[86], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[89], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[103], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[105], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[110], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[111], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[113], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[115], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[116], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[117], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate030.coverRows = (#[#[10, 11, 14], #[12, 13, 15], #[16], #[15], #[17], #[18], #[0, 1], #[19], #[20], #[21], #[2, 3], #[22], #[14], #[23], #[24], #[25], #[14], #[26], #[27], #[4, 5], #[28], #[15], #[29], #[6, 7], #[30], #[31], #[32], #[33], #[34], #[35], #[2], #[6], #[36], #[37], #[38], #[3], #[8], #[39], #[40], #[41], #[42], #[7], #[15], #[43], #[44], #[45], #[0], #[4], #[46], #[47], #[48], #[49], #[50], #[1], #[14], #[51], #[52], #[53], #[54], #[5], #[9], #[55], #[56], #[57], #[8], #[58], #[59], #[60], #[10], #[11], #[61], #[62], #[12], #[13], #[63], #[64], #[65], #[66], #[67], #[68], #[69], #[70], #[71], #[72], #[73], #[74], #[75], #[76], #[77], #[78], #[79], #[80], #[81], #[82], #[83], #[84], #[11], #[10], #[85], #[86], #[13], #[12], #[87], #[88], #[89], #[90], #[91], #[92], #[9], #[93], #[94], #[95], #[96], #[97], #[98], #[99], #[100], #[101]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate030 q certificate030.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case030_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case030_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate030.rows.toList.all (rowB certificate030) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate030.pool.size).all (localCoverB certificate030) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate030 < certificate030.denominator * (deletedCount certificate030+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 100) (0 : ZMod 3) := by
  have hs : certificate030.blockers.size = 6561 := by
    simp only [certificate030, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate030.normal) certificate030.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
