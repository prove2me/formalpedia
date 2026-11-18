-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCutoffLogIntegralAllPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:20:46.339206+00:00
-- url     : https://prove2.me/submissions/402edb28-0d6f-4f8d-910b-eecb1bb7cbe6

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffHighIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLowIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! The signed compensation difference equals the positive frequency logarithm. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
      Real.log z := by
  by_cases h : 1 ≤ z
  · exact Kyprianou.Ch01.stableAlphaOneCutoffHighIntegral z h
  · exact Kyprianou.Ch01.stableAlphaOneCutoffLowIntegral z hz (le_of_lt (lt_of_not_ge h))
