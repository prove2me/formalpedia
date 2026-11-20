-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneNegativePowerAntiderivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:13:02.157839+00:00
-- url     : https://prove2.me/submissions/abfc76ea-18b5-4741-83ad-afd130a1cde7

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Complex MeasureTheory Set
set_option autoImplicit false

/-- Positive real power antiderivative for the stable compensated kernel. -/
theorem solution
    (alpha r : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => t ^ (-alpha) / (-alpha))
      (r ^ (-(alpha + 1))) r := by
  have hα : -alpha ≠ 0 := by linarith
  have hpow : HasDerivAt (fun t : ℝ => t ^ (-alpha))
      ((-alpha) * r ^ (-alpha - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hr.ne')
  have hcoeff :
      ((-alpha) * r ^ (-alpha - 1)) / (-alpha) =
        r ^ (-(alpha + 1)) := by
    rw [show -alpha - 1 = -(alpha + 1) by ring]
    field_simp
  simpa only [hcoeff] using hpow.div_const (-alpha)
