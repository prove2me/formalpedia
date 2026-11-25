-- Prove2me | solution 1 for Kyprianou.Ch04.l2NormSquareIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:38:07.724588+00:00
-- url     : https://prove2.me/submissions/8d1d15e1-66db-4482-be65-81deb121352b

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The square of the real L² norm is the integrated square. -/
theorem solution {α : Type} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : MemLp g 2 μ) :
    (eLpNorm g 2 μ).toReal ^ 2 = ∫ x, (g x)^2 ∂μ := by
  have hnorm : eLpNorm g 2 μ =
      (ENNReal.ofReal (∫ x, (g x)^2 ∂μ)) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2]
    have hpoint : (fun x => ‖g x‖ₑ ^ (2 : ℝ)) = fun x => ENNReal.ofReal ((g x)^2) := by
      funext x
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [hpoint, ← ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)]
  have hsq : (eLpNorm g 2 μ)^2 = ENNReal.ofReal (∫ x, (g x)^2 ∂μ) := by
    rw [← ENNReal.rpow_two, hnorm, ← ENNReal.rpow_mul]
    norm_num
  have h := congrArg ENNReal.toReal hsq
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)] at h
  exact h
