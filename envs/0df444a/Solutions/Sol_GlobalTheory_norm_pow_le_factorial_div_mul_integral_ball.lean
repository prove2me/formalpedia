-- Prove2me | solution 1 for GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:40.516782+00:00
-- url     : https://prove2.me/submissions/7e15e483-a2c3-4faa-b740-18c9b152db26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_norm_pow_le_inv_measure_mul_integral_ball
import Theorems.Thm_GlobalTheory_volume_ball_complex

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution {a : E} {r : ℝ} (hr : 0 < r) {φ : E → H}
    (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ)
    (hi : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r)) :
    ‖φ a‖ ^ n ≤ (Module.finrank ℂ E).factorial /
      (π ^ Module.finrank ℂ E * r ^ (2 * Module.finrank ℂ E)) * ∫ z in ball a r, ‖φ z‖ ^ n := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  have h := norm_pow_le_inv_measure_mul_integral_ball volume hr hφ n hi
  rwa [Measure.real, volume_ball_complex a hr, ENNReal.toReal_ofReal (by positivity), inv_div] at h
end GlobalTheory
