-- Prove2me | solution 1 for HardyCapset20261020.Cert.case149_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-21T04:23:05.465722+00:00
-- url     : https://prove2.me/submissions/900686a7-6996-4b6c-8d1b-e6931e0ea028

import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_0
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_1
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_2
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_3
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_4
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_5
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_6
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_7
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_8
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_9
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_10
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_11
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_12
import Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_13
import Definitions.Def_HardyCapsetEvaluationData149V420261021
import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate14920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case149_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case149_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate149
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate149.normal = (evaluationDataV4149_normal : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate149.level = (evaluationDataV4149_level : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate149.pool = (evaluationDataV4149_pool : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate149.denominator = (evaluationDataV4149_denominator : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate149.rows = (evaluationDataV4149_rows : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate149.coverRows = (evaluationDataV4149_coverRows : Array (Array Nat)) := rfl


set_option autoImplicit false
namespace HardyCapset20261020.Cert
attribute [-cbv_eval] cost_list
@[cbv_eval] theorem cost_fold (c : Certificate) :
    cost c = (c.rows.toList.map (fun r => r.weight * r.bound)).sum := by
  have h (a : Array Row) : (List.range a.size).map (fun i => a[i]!) = a.toList := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      have hi : i < a.size := by simpa using h₂
      simp only [List.getElem_map, List.getElem_range]
      simpa only [Array.getElem_toList] using getElem!_pos a i hi
  rw [cost_list, ← h c.rows, List.map_map]
  rfl
end HardyCapset20261020.Cert
private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate149 q certificate149.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case149_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case149_blockers1 ⟨q-3328,by omega⟩
private theorem finite_checks (q : Nat) (hq : q < 445) :
    ((if q < certificate149.rows.size then rowB certificate149 certificate149.rows[q]! else true) &&
    (if q < certificate149.pool.size then localCoverB certificate149 q else true)) = true := by
  by_cases h0 : q < 32
  · simpa only [Nat.zero_add] using case149_finite32_0 ⟨q,by omega⟩
  by_cases h1 : q < 64
  · have he : 32+(q-32) = q := by omega
    simpa only [he] using case149_finite32_1 ⟨q-32,by omega⟩
  by_cases h2 : q < 96
  · have he : 64+(q-64) = q := by omega
    simpa only [he] using case149_finite32_2 ⟨q-64,by omega⟩
  by_cases h3 : q < 128
  · have he : 96+(q-96) = q := by omega
    simpa only [he] using case149_finite32_3 ⟨q-96,by omega⟩
  by_cases h4 : q < 160
  · have he : 128+(q-128) = q := by omega
    simpa only [he] using case149_finite32_4 ⟨q-128,by omega⟩
  by_cases h5 : q < 192
  · have he : 160+(q-160) = q := by omega
    simpa only [he] using case149_finite32_5 ⟨q-160,by omega⟩
  by_cases h6 : q < 224
  · have he : 192+(q-192) = q := by omega
    simpa only [he] using case149_finite32_6 ⟨q-192,by omega⟩
  by_cases h7 : q < 256
  · have he : 224+(q-224) = q := by omega
    simpa only [he] using case149_finite32_7 ⟨q-224,by omega⟩
  by_cases h8 : q < 288
  · have he : 256+(q-256) = q := by omega
    simpa only [he] using case149_finite32_8 ⟨q-256,by omega⟩
  by_cases h9 : q < 320
  · have he : 288+(q-288) = q := by omega
    simpa only [he] using case149_finite32_9 ⟨q-288,by omega⟩
  by_cases h10 : q < 352
  · have he : 320+(q-320) = q := by omega
    simpa only [he] using case149_finite32_10 ⟨q-320,by omega⟩
  by_cases h11 : q < 384
  · have he : 352+(q-352) = q := by omega
    simpa only [he] using case149_finite32_11 ⟨q-352,by omega⟩
  by_cases h12 : q < 416
  · have he : 384+(q-384) = q := by omega
    simpa only [he] using case149_finite32_12 ⟨q-384,by omega⟩
  have he : 416+(q-416) = q := by omega
  simpa only [he] using case149_finite32_13 ⟨q-416,by omega⟩

private theorem finite_row_size : certificate149.rows.size = 338 := by
  rw [evaluation_rows]
  rfl
private theorem finite_pool_size : certificate149.pool.size = 445 := by
  rw [evaluation_pool]
  rfl
private theorem rows_check : certificate149.rows.toList.all (rowB certificate149) = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hrow)
  have hj' : j < 338 := by simpa only [finite_row_size] using hj
  have h := (Bool.and_eq_true_iff.mp (finite_checks j (by omega))).1
  rw [if_pos hj, getElem!_pos certificate149.rows j hj, he] at h
  exact h
private theorem covers_check : (List.range certificate149.pool.size).all (localCoverB certificate149) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  have hj'' : j < 445 := by simpa only [finite_pool_size] using hj'
  have h := (Bool.and_eq_true_iff.mp (finite_checks j (by omega))).2
  simpa only [if_pos hj'] using h

private theorem evaluated_cost : cost certificate149 = 204000110 := by
  rw [cost_fold, evaluation_rows]
  rfl
private theorem evaluated_deleted : deletedCount certificate149 = 204 := by
  decide_cbv
private theorem cost_check : decide (cost certificate149 < certificate149.denominator * (deletedCount certificate149+1)) = true := by
  rw [evaluated_cost, evaluated_deleted, evaluation_denominator]
  decide_cbv
theorem solution : CompletionBound (decode 1075) (1 : ZMod 3) := by
  have hs : certificate149.blockers.size = 6561 := by
    simp only [certificate149, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate149.normal) certificate149.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
