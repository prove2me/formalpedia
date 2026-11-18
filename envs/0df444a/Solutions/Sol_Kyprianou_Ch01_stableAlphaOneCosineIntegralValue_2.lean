-- Prove2me | solution 2 for Kyprianou.Ch01.stableAlphaOneCosineIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:39:04.118599+00:00
-- url     : https://prove2.me/submissions/b63792b5-f69e-4bc1-bc8a-d0e1dd943684

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineRealToLintegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineLintegralEqualsRational
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneRationalLintegralToReal
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneRationalIntegralValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

/-! Exact original α=1 stable cosine π/2 integral via proved Tonelli identities. -/
theorem solution :
    (∫ x in Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2) = Real.pi / 2 := by
  rw [Kyprianou.Ch01.stableAlphaOneCosineRealToLintegral,
      Kyprianou.Ch01.stableAlphaOneCosineLintegralEqualsRational,
      Kyprianou.Ch01.stableAlphaOneRationalLintegralToReal]
  exact Kyprianou.Ch01.stableAlphaOneRationalIntegralValue
