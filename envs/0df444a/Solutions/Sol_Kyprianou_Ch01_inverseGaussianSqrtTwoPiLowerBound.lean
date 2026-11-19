-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianSqrtTwoPiLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:59:42.115241+00:00
-- url     : https://prove2.me/submissions/b9471485-b804-49dc-b771-50dbcca8ae01

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
set_option autoImplicit false

/-- The inverse Gaussian normalising square root is bounded below by one. -/
theorem solution : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by
    have hpi := Real.one_le_pi_div_two
    nlinarith)
