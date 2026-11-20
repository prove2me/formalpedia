-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDoubleComplexTilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:39:41.34845+00:00
-- url     : https://prove2.me/submissions/4c476cc4-c471-4a5c-ada7-b268a3db64aa

import Mathlib
open Complex Real ComplexOrder
set_option autoImplicit false

theorem solution
    (b theta : ℝ) :
    (2 : ℂ) *
      (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ)) =
      ((b ^ 2 : ℝ) : ℂ) - 2 * Complex.I * (theta : ℂ) := by
  push_cast
  ring
