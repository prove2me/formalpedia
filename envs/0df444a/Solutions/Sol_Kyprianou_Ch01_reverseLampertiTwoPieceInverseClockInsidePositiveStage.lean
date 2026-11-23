-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockInsidePositiveStage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:36:43.770478+00:00
-- url     : https://prove2.me/submissions/1ec69fbe-9b66-4d67-a967-769dbad1fefb

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationBracketFromCrossing
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPiecePositiveClockCrossingWitness
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hPost : 0 < y + j - 1)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    ∃ s : ℝ≥0, a ≤ (s : ℝ) ∧ (s : ℝ) < b ∧
      inverseReciprocalOccupation X t ω = (s : WithTop ℝ≥0) := by
  obtain ⟨c, hc, hBefore, hCross⟩ :=
    Kyprianou.Ch01.reverseLampertiTwoPiecePositiveClockCrossingWitness
      X ω y j hy t a b ha hAB hPrefix hMiddle hPost hFirst hSecond
  let aNN : ℝ≥0 := Real.toNNReal a
  have haNN : (aNN : ℝ) = a := Real.coe_toNNReal a ha.le
  have hBeforeNN (u : ℝ≥0) (hu : u < aNN) :
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞) := by
    apply hBefore u
    calc (u : ℝ) < (aNN : ℝ) := NNReal.coe_lt_coe.mpr hu
      _ = a := haNN
  obtain ⟨s, hsLower, hsUpper, hTheta⟩ :=
    Kyprianou.Ch01.inverseReciprocalOccupationBracketFromCrossing
      X ω t aNN c hBeforeNN hCross
  refine ⟨s, ?_, ?_, hTheta⟩
  · have hh := NNReal.coe_le_coe.mpr hsLower
    simpa only [haNN] using hh
  · exact (NNReal.coe_le_coe.mpr hsUpper).trans_lt hc
