-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_exp_tilt_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:41:16.737009+00:00
-- url     : https://prove2.me/submissions/76bbc49b-78bf-4eb5-96bf-d3f1bcc0c353

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Exponential tilting shifts the argument of the nonnegative Laplace integral. -/
theorem solution (μ : Measure ℝ) (a : ℝ≥0∞) (s : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂
      μ.withDensity (fun x => a * ENNReal.ofReal (Real.exp x))) =
      a * ∫⁻ x, ENNReal.ofReal (Real.exp ((s+1)*x)) ∂μ := by
  have hf : Measurable (fun x : ℝ => a * ENNReal.ofReal (Real.exp x)) :=
    measurable_const.mul (Real.continuous_exp.measurable.ennreal_ofReal)
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (s*x))) :=
    (measurable_const.mul measurable_id).exp.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul μ hf hg]
  have hh : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp ((s+1)*x))) :=
    (measurable_const.mul measurable_id).exp.ennreal_ofReal
  rw [← lintegral_const_mul a hh]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 3
  ring
