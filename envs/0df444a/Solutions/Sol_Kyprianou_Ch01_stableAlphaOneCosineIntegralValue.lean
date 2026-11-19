-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:16:49.151575+00:00
-- url     : https://prove2.me/submissions/e77f6f96-8b08-4333-97f5-ad3fd81e6ffd

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineEqualsSincSquare
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneSincSquaredIntegralValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false

/-! Preserve the original cosine value by exact half-angle and sinc-square evaluation. -/
theorem solution :
    (∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2) = Real.pi / 2 := by
  rw [Kyprianou.Ch01.stableAlphaOneCosineEqualsSincSquare]
  exact Kyprianou.Ch01.stableAlphaOneSincSquaredIntegralValue
