-- Prove2me | solution 1 for HardyCapset20261020.Cert.case023_finite32_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:36:58.867294+00:00
-- url     : https://prove2.me/submissions/246daafb-a8d5-4ac8-b4aa-98c67615f60d

import Definitions.Def_HardyCapsetEvaluationData023V420261021
import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate02320261021
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate023
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate023.normal = (evaluationDataV4023_normal : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate023.level = (evaluationDataV4023_level : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate023.pool = (evaluationDataV4023_pool : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate023.denominator = (evaluationDataV4023_denominator : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate023.rows = (evaluationDataV4023_rows : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate023.coverRows = (evaluationDataV4023_coverRows : Array (Array Nat)) := rfl


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

private def chk (n : ℕ) : Bool :=
  (if n < certificate023.rows.size then rowB certificate023 certificate023.rows[n]! else true) &&
    (if n < certificate023.pool.size then localCoverB certificate023 n else true)

private theorem blk0 : ∀ k : Fin 4, chk (320 + k.val) = true := by
  decide +kernel

private theorem blk1 : ∀ k : Fin 4, chk (324 + k.val) = true := by
  decide +kernel

private theorem blk2 : ∀ k : Fin 4, chk (328 + k.val) = true := by
  decide +kernel

private theorem blk3 : ∀ k : Fin 4, chk (332 + k.val) = true := by
  decide +kernel

private theorem blk4 : ∀ k : Fin 4, chk (336 + k.val) = true := by
  decide +kernel

private theorem blk5 : ∀ k : Fin 4, chk (340 + k.val) = true := by
  decide +kernel

private theorem blk6 : ∀ k : Fin 4, chk (344 + k.val) = true := by
  decide +kernel

private theorem blk7 : ∀ k : Fin 4, chk (348 + k.val) = true := by
  decide +kernel

theorem solution (j : Fin 32) :
    ((if 320+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[320+j.val]! else true) &&
    (if 320+j.val < certificate023.pool.size then localCoverB certificate023 (320+j.val) else true)) = true := by
  obtain ⟨n, hn⟩ := j
  show chk (320 + n) = true
  have hk : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e : 320 + n = (320 + 4 * (n / 4)) + n % 4 := by omega
  have hb : n / 4 < 8 := by omega
  rw [e]
  generalize n / 4 = b at hb
  match b, hb with
  | 0, _ => exact blk0 ⟨n % 4, hk⟩
  | 1, _ => exact blk1 ⟨n % 4, hk⟩
  | 2, _ => exact blk2 ⟨n % 4, hk⟩
  | 3, _ => exact blk3 ⟨n % 4, hk⟩
  | 4, _ => exact blk4 ⟨n % 4, hk⟩
  | 5, _ => exact blk5 ⟨n % 4, hk⟩
  | 6, _ => exact blk6 ⟨n % 4, hk⟩
  | 7, _ => exact blk7 ⟨n % 4, hk⟩
  | _ + 8, h => exact absurd h (by omega)
