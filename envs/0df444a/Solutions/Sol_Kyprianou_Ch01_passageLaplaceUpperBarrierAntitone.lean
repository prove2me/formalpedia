-- Prove2me | solution 1 for Kyprianou.Ch01.passageLaplaceUpperBarrierAntitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:13:27.332198+00:00
-- url     : https://prove2.me/submissions/691106b7-a7e3-4a03-830f-cbe63bb618f2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceAntitoneStoppingTime
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Higher strict upper barriers have no larger discounted first-passage payoffs. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (a b : ℝ) (hab : a ≤ b)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    passageLaplace (firstUpperPassage X b) q ω ≤
      passageLaplace (firstUpperPassage X a) q ω := by
  exact Kyprianou.Ch01.passageLaplaceAntitoneStoppingTime
    (firstUpperPassage X a) (firstUpperPassage X b) q hq
    (fun ω => Kyprianou.Ch01.firstUpperPassageBarrierMonotone
      X a b hab ω) ω
