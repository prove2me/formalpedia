-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiImageOfMeasurableWalk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:27:22.199355+00:00
-- url     : https://prove2.me/submissions/13f3d719-4287-4625-9c4d-7f64a7797576
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_lampertiStoppedClockMeasurable
import Theorems.Thm_Kyprianou_Ch01_evalIntegerWalkAtWithTopTime

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable
      (fun p : Ω × ℝ≥0 => compoundPoissonToBranching X p.2 p.1) := by
  have hclock := lampertiStoppedClockMeasurable X hX
  change Measurable
    (fun p : Ω × ℝ≥0 =>
      match min (inverseReciprocalOccupation X p.2 p.1)
          (firstNegativePassage X p.1) with
      | none => (0 : ℤ)
      | some s => X s p.1)
  exact evalIntegerWalkAtWithTopTime X hX _
    (by simpa using hclock)
