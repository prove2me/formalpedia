-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneComplexLaplaceFrequencyOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:19:02.492215+00:00
-- url     : https://prove2.me/submissions/76c7f61f-4fdd-4ed9-a8b6-391d0482f9fd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set
set_option autoImplicit false
/-! Positive Laplace transform of exp(i x) with real damping a>0. -/
theorem solution
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      Complex.exp (((-(a : ℂ)) + Complex.I) * (x : ℂ))) =
      ((a : ℂ) - Complex.I)⁻¹ := by
  have hneg : ((-(a : ℂ)) + Complex.I).re < 0 := by
    simpa using (neg_neg_of_pos ha)
  have h := integral_exp_mul_complex_Ioi
    (a := (-(a : ℂ)) + Complex.I) hneg (0 : ℝ)
  simpa [Complex.exp_zero, div_eq_mul_inv, neg_inv, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h
