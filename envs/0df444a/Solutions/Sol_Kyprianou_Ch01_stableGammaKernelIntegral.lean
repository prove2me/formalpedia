-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaKernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:59:49.034284+00:00
-- url     : https://prove2.me/submissions/7bf12b2b-d02a-4505-affe-ae5f2219a4d9

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Real
set_option autoImplicit false

/-- The scaled positive Gamma Laplace kernel at exponent minus alpha. -/
theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(u * x)) * x ^ (-alpha) ∂volume) =
      (1 / u) ^ (1 - alpha) * Real.Gamma (1 - alpha) := by
  have ha : 0 < 1 - alpha := by linarith
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1 - alpha) (r := u) ha hu
  have heq : (1 - alpha) - 1 = -alpha := by ring
  simpa only [heq, mul_comm] using h
