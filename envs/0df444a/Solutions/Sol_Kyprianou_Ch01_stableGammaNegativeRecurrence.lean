-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaNegativeRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:58:09.219199+00:00
-- url     : https://prove2.me/submissions/e03becfd-e746-4393-87a4-3cdb2c57d638

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Real
set_option autoImplicit false

/-- Gamma(1-alpha) = -alpha * Gamma(-alpha) away from the poles. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    Real.Gamma (-alpha) = -(Real.Gamma (1 - alpha)) / alpha := by
  have hne : -alpha ≠ 0 := by linarith
  have hr := Real.Gamma_add_one hne
  have heq : Real.Gamma (1 - alpha) = -alpha * Real.Gamma (-alpha) := by
    convert hr using 1 <;> ring
  apply (eq_div_iff (ne_of_gt h0)).2
  nlinarith [heq]
