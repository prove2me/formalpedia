-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiStoppedClockMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T14:20:26.067745+00:00
-- url     : https://prove2.me/submissions/d32b6ba1-adb8-4fd6-b8cf-80f4fb4f7b96
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassageMeasurable
import Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationJointlyMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        min (inverseReciprocalOccupation X p.2 p.1)
          (firstNegativePassage X p.1)) := by
  have hinv := inverseReciprocalOccupationJointlyMeasurable X hX
  have hpass : Measurable (fun p : Ω × ℝ≥0 => firstNegativePassage X p.1) :=
    (firstNegativePassageMeasurable X hX).comp measurable_fst
  exact hinv.min hpass
