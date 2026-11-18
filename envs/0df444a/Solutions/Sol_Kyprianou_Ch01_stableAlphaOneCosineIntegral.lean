-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:40:11.241199+00:00
-- url     : https://prove2.me/submissions/eb23e5c3-8e9f-4db8-bc7f-8bef2aedce17

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosinePositiveIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegralValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem solution :
    IntegrableOn
      (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (1 - Real.cos r) / r ^ 2 ∂volume) = Real.pi / 2 := by
  exact ⟨Kyprianou.Ch01.stableAlphaOneCosinePositiveIntegrable,
    Kyprianou.Ch01.stableAlphaOneCosineIntegralValue⟩
