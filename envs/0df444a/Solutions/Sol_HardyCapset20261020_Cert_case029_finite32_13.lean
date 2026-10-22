-- Prove2me | solution 1 for HardyCapset20261020.Cert.case029_finite32_13
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-21T03:59:27.563134+00:00
-- url     : https://prove2.me/submissions/c0b01b33-115d-4f50-ab8d-43880a3f421e

import Definitions.Def_HardyCapsetEvaluationData029V420261021
import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate02920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate029
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate029.normal = (evaluationDataV4029_normal : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate029.level = (evaluationDataV4029_level : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate029.pool = (evaluationDataV4029_pool : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate029.denominator = (evaluationDataV4029_denominator : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate029.rows = (evaluationDataV4029_rows : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate029.coverRows = (evaluationDataV4029_coverRows : Array (Array Nat)) := rfl


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

private theorem interval_checked :
    (List.range 32).all (fun k => ((if 416+k < certificate029.rows.size then rowB certificate029 certificate029.rows[416+k]! else true) &&
    (if 416+k < certificate029.pool.size then localCoverB certificate029 (416+k) else true))) = true := by
  decide_cbv
theorem solution (j : Fin 32) :
    ((if 416+j.val < certificate029.rows.size then rowB certificate029 certificate029.rows[416+j.val]! else true) &&
    (if 416+j.val < certificate029.pool.size then localCoverB certificate029 (416+j.val) else true)) = true := by
  exact List.all_eq_true.mp interval_checked j.val (List.mem_range.mpr j.isLt)
#print axioms solution
