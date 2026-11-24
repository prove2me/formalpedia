-- Prove2me | solution 1 for GlobalTheory.norm_pow_le_inv_measure_mul_integral_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:26.637444+00:00
-- url     : https://prove2.me/submissions/7b7032c2-f926-4916-b7f2-2b3a3cce352e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_norm_pow_mul_integral_ball_le

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
    {r : ℝ} (hr : 0 < r) {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ)
    (hi : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r) μ) :
    ‖φ a‖ ^ n ≤ (μ.real (ball a r))⁻¹ * ∫ z in ball a r, ‖φ z‖ ^ n ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h := norm_pow_mul_integral_ball_le μ hφ (w := fun _ => 1) measurable_const
    (fun _ _ => zero_le_one) n (integrableOn_const measure_ball_lt_top.ne) (by simpa using hi)
  have h0 : 0 < μ.real (ball a r) :=
    ENNReal.toReal_pos (measure_ball_pos μ a hr).ne' measure_ball_lt_top.ne
  rw [le_inv_mul_iff₀ h0, mul_comm]
  simpa using h
end GlobalTheory
