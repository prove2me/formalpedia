-- Prove2me | solution 1 for GlobalTheory.ExpDivision.exists_division
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:15.931026+00:00
-- url     : https://prove2.me/submissions/c9fe446c-d73c-4eba-ba78-4b6d36afd736

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_div
import Theorems.Thm_GlobalTheory_ExpDivision_mul_quot
import Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_quot
import Theorems.Thm_GlobalTheory_ExpDivision_quot_neg
import Theorems.Thm_GlobalTheory_ExpDivision_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ),
    (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  set a : ℝ := 2 * Real.pi with ha
  set b : ℝ := 2 * Real.pi * √2 with hb
  set E : ℝ → ℂ := fun t => quot a t * quot (-a) t + quot b t * quot (-b) t with hE
  have hEt : E.HasTemperateGrowth :=
    ((hasTemperateGrowth_quot a).mul (hasTemperateGrowth_quot (-a))).add
      ((hasTemperateGrowth_quot b).mul (hasTemperateGrowth_quot (-b)))
  have hn : ∀ t, ‖E t‖ = ‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 := by
    intro t
    have : E t = ((‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hE, quot_neg, Complex.mul_conj']
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hl : ∀ t, 1 ≤ 8 * (1 + ‖t‖) ^ 4 * ‖E t‖ := by
    intro t
    have h := lower t
    rw [← ha, ← hb] at h
    rw [hn, Real.norm_eq_abs]
    have h2 := one_le_pow₀ (n := 2) h
    have h3 : (‖quot a t‖ + ‖quot b t‖) ^ 2 ≤ 2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖quot a t‖ - ‖quot b t‖)]
    calc (1 : ℝ) ≤ _ := h2
      _ = 4 * (1 + |t|) ^ 4 * (‖quot a t‖ + ‖quot b t‖) ^ 2 := by ring
      _ ≤ 4 * (1 + |t|) ^ 4 * (2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2)) := by gcongr
      _ = _ := by ring
  have h0 : ∀ t, E t ≠ 0 := by
    intro t h
    have := hl t
    rw [h] at this
    norm_num at this
  have hM : ∀ t, ‖(E t)⁻¹‖ ≤ 8 * (1 + ‖t‖) ^ 4 := by
    intro t
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.2 (h0 t))]
    exact hl t
  refine ⟨2, ![a, b], ![fun t => quot (-a) t / E t, fun t => quot (-b) t / E t], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
  · intro t
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.ofReal_mul a t, Complex.ofReal_mul b t, ← mul_quot, ← mul_quot]
    have := h0 t
    field_simp
    simp only [hE]
end GlobalTheory.ExpDivision
