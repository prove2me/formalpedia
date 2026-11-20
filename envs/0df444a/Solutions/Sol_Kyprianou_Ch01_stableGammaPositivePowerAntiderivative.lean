-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaPositivePowerAntiderivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:20:36.625933+00:00
-- url     : https://prove2.me/submissions/21a74526-c1b8-4a58-a0f2-f58948deec6c

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Complex MeasureTheory Set
set_option autoImplicit false

/-- Positive-real antiderivative of the alpha-stable singular power. -/
theorem solution
    (alpha r : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => t ^ (-alpha) / (-alpha))
      (r ^ (-alpha - 1)) r := by
  have hα : -alpha ≠ 0 := by linarith
  have hpow : HasDerivAt (fun t : ℝ => t ^ (-alpha))
      ((-alpha) * r ^ (-alpha - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hr.ne')
  have hcoeff :
      ((-alpha) * r ^ (-alpha - 1)) / (-alpha) =
        r ^ (-alpha - 1) := by
    field_simp
  simpa only [hcoeff] using hpow.div_const (-alpha)
