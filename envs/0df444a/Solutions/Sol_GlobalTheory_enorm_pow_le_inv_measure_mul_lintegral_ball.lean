-- Prove2me | solution 1 for GlobalTheory.enorm_pow_le_inv_measure_mul_lintegral_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:37.996554+00:00
-- url     : https://prove2.me/submissions/4c20f805-ae6e-499d-a081-c0afba741668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_ball_le_of_centre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} (hr : 0 < r) {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ) :
    ‖φ a‖ₑ ^ n ≤ (μ (ball a r))⁻¹ * ∫⁻ z in ball a r, ‖φ z‖ₑ ^ n ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h := enorm_pow_mul_lintegral_ball_le_of_centre μ hφ (w := fun _ => 1) measurable_const n
  simp only [lintegral_const, one_mul, mul_one, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter] at h
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos μ a hr).ne')
      (Or.inl measure_ball_lt_top.ne)]
  exact h
end GlobalTheory
