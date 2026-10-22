-- Prove2me | solution 1 for HardyCapset20261020.Cert.case172_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T22:58:20.899891+00:00
-- url     : https://prove2.me/submissions/fdc7ccf8-7216-4648-ae6c-879a6977452d

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate17220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case172_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case172_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate172
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate172.normal = (2223 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate172.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate172.pool = (#[289, 290, 294, 307, 308, 312, 532, 533, 534, 550, 551, 552, 776, 777, 780, 794, 795, 798, 1504, 1506, 1509, 1522, 1524, 1527, 2209, 2210, 2212, 2213, 2223, 2386, 2387, 2388, 2391, 2454, 2628, 2694, 2871, 2936, 3114, 3177, 3280, 3281, 3283, 3361, 3420, 3523, 3526, 3527, 3607, 3664, 3843, 3906, 4009, 4010, 4013, 4091, 4149, 4253, 4255, 4256, 4337, 4387, 4388, 4390, 4391, 4446, 4528, 4529, 4530, 4533, 4632, 4770, 4872, 5013, 5114, 5256, 5355, 5503, 5584, 5585, 5587, 5598, 5749, 5827, 5830, 5831, 5842, 5985, 6084, 6233, 6313, 6314, 6317, 6327, 6479, 6557, 6559, 6560] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate172.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate172.rows = (#[{ vars := #[2, 35, 65], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[5, 28, 72], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[8, 33, 65], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[11, 28, 70], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[12, 49, 65], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[15, 28, 86], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 37, 65], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[21, 28, 74], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[28, 40, 60], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[28, 43, 59], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[28, 46, 55], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[28, 48, 53], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[65, 77, 97], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[65, 78, 94], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[65, 82, 91], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[65, 84, 89], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[0], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[1], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[3], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[4], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[6], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[7], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[19], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[20], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[23], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[27], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[30], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[31], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[32], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[41], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[42], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[54], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[56], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[64], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[73], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[83], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[96], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate172.coverRows = (#[#[16], #[17], #[0], #[18], #[19], #[1], #[20], #[21], #[2], #[22], #[23], #[3], #[4], #[24], #[25], #[5], #[26], #[27], #[6], #[28], #[29], #[7], #[30], #[31], #[32], #[33], #[34], #[35], #[1, 3, 5, 7, 8, 9, 10, 11], #[36], #[37], #[38], #[39], #[2], #[40], #[0], #[41], #[6], #[42], #[43], #[8], #[44], #[45], #[9], #[46], #[47], #[10], #[48], #[11], #[4], #[49], #[50], #[51], #[11], #[52], #[10], #[53], #[54], #[55], #[9], #[8], #[56], #[57], #[58], #[59], #[0, 2, 4, 6, 12, 13, 14, 15], #[60], #[61], #[62], #[63], #[3], #[64], #[1], #[65], #[7], #[66], #[67], #[12], #[13], #[68], #[69], #[70], #[14], #[71], #[15], #[72], #[5], #[73], #[74], #[15], #[75], #[14], #[76], #[77], #[13], #[78], #[79], #[12]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate172 q certificate172.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case172_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case172_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate172.rows.toList.all (rowB certificate172) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate172.pool.size).all (localCoverB certificate172) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate172 < certificate172.denominator * (deletedCount certificate172+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 2223) (0 : ZMod 3) := by
  have hs : certificate172.blockers.size = 6561 := by
    simp only [certificate172, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate172.normal) certificate172.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
