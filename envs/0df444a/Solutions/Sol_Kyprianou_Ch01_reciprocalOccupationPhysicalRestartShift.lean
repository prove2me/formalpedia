-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationPhysicalRestartShift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:17:14.773009+00:00
-- url     : https://prove2.me/submissions/ccba485f-bda4-43a5-83b5-45c5493c9b1a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPhysicalPrefixExact
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPhysicalIntervalCut
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationShiftedTailLIntegral
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω)
    (u : ℝ≥0) (hu : A ≤ (u : ℝ)) :
    reciprocalOccupation X u ω =
      ENNReal.ofReal (A / (y : ℝ)) +
        reciprocalOccupation Y (Real.toNNReal ((u : ℝ) - A)) ω := by
  have hPrefixExact :=
    reciprocalOccupationPhysicalPrefixExact
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative
  have hCut :=
    reciprocalOccupationPhysicalIntervalCut
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative u hu
  have hTail :=
    reciprocalOccupationShiftedTailLIntegral
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative u hu
  rw [hCut, hPrefixExact, hTail]
