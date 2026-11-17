-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicCompensatedExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:17:42.933203+00:00
-- url     : https://prove2.me/submissions/d01d7373-3ac4-4422-bd44-0e9dc6e36bdd

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpComplexExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-! The compensated logarithmic jump series is the compound-Poisson exponent. -/
theorem solution
    (q z : ℂ) (hq : ‖q‖ < 1) (hqz : ‖q * z‖ < 1) :
    (∑' n : ℕ,
      q ^ (n + 1) / ((n : ℂ) + 1) *
        (z ^ (n + 1) - 1)) =
      Complex.log (1 - q) - Complex.log (1 - q * z) := by
  rw [← Kyprianou.Ch01.logarithmicJumpComplexExponent q z hq hqz]
  apply tsum_congr
  intro n
  rw [mul_pow]
  ring
