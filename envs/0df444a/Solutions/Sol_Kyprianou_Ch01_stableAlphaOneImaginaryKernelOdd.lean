-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneImaginaryKernelOdd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:27:20.459212+00:00
-- url     : https://prove2.me/submissions/28d2b6e8-45ad-4d0c-890b-f6643baeceb1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! The imaginary compensated alpha-one Lévy kernel is odd in frequency. -/
theorem solution
    (z r : ℝ) :
    (((-z) * r) * (if r < 1 then (1 : ℝ) else 0) -
      Real.sin ((-z) * r)) / r ^ 2 =
      -(((z * r) * (if r < 1 then (1 : ℝ) else 0) -
        Real.sin (z * r)) / r ^ 2) := by
  simp only [neg_mul, Real.sin_neg]
  ring
