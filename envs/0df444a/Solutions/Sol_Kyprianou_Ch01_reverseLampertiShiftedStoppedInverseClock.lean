-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiShiftedStoppedInverseClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:17:34.565525+00:00
-- url     : https://prove2.me/submissions/539ac066-298a-4cf3-ba5f-b3d0289767b7

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedInverseReciprocalOccupation
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedFirstNegativePassage
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
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) =
      (((Real.toNNReal A : ℝ≥0) : WithTop ℝ≥0) +
        min
          (inverseReciprocalOccupation Y
            (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω)
          (firstNegativePassage Y ω)) := by
  have hInverse :=
    reverseLampertiShiftedInverseReciprocalOccupation
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative
  have hPass :=
    reverseLampertiShiftedFirstNegativePassage
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative
  simpa only [hInverse, hPass, min_add_add_left]
