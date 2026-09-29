-- Prove2me | solution 1 for KobayashiMaskawa1973.one_div_eight_mul_sqrt_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:31:23.171196+00:00
-- url     : https://prove2.me/submissions/ddfc7316-23f8-4dc3-8f37-74066562fb4d

import Mathlib

theorem solution :
    (1 / (8 * Real.sqrt 2) : ℝ) ≠ 0 := by
  positivity
