-- Prove2me | solution 1 for Kyprianou.Ch01.realScaledIntervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:01:37.494824+00:00
-- url     : https://prove2.me/submissions/64be67d9-8e2d-4512-bb77-c29ecea1a2eb

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory intervalIntegral
set_option autoImplicit false

theorem solution
    (c t : ℝ) (f : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..t, c * f (c * s)) =
      (∫ a in (0 : ℝ)..c * t, f a) := by
  simpa only [intervalIntegral.integral_const_mul, mul_zero] using
    (intervalIntegral.mul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := t) (f := f) c)
