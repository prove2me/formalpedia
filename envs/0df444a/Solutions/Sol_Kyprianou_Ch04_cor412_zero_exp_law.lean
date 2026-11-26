-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_zero_exp_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:03.330469+00:00
-- url     : https://prove2.me/submissions/483ee6ce-57f6-4105-84cd-83a52fe3cee5

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- A zero exponential integral forces the measure to vanish. -/
theorem solution (μ : Measure ℝ)
    (h : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = 0) : μ = 0 := by
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp x)
  have hf : Measurable f := Real.continuous_exp.measurable.ennreal_ofReal
  have hzero : μ.withDensity f = 0 := by
    rw [← Measure.measure_univ_eq_zero, withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]
    exact h
  rw [← withDensity_inv_same (μ := μ) hf (Eventually.of_forall fun x => by
    simp [f, Real.exp_pos]) (Eventually.of_forall fun x => ENNReal.ofReal_ne_top),
    hzero]
  simp
