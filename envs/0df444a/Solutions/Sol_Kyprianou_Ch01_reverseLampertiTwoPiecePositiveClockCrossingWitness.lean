-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoPiecePositiveClockCrossingWitness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:39:28.513848+00:00
-- url     : https://prove2.me/submissions/ffed66d2-27e6-40d6-a1a3-2623c5964906
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_twoPieceOccupationBeforeFirstLePhysicalTime
import Theorems.Thm_Kyprianou_Ch01_twoPieceOccupationCrossesPhysicalBeforeSecond
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
    ∃ c : ℝ≥0, (c : ℝ) < b ∧
      (∀ u : ℝ≥0, (u : ℝ) < a →
        reciprocalOccupation X u ω ≤ (t : ℝ≥0∞)) ∧
      (t : ℝ≥0∞) < reciprocalOccupation X c ω := by
  obtain ⟨c, hc, hCross⟩ :=
    Kyprianou.Ch01.twoPieceOccupationCrossesPhysicalBeforeSecond
      X ω y j hy t a b ha hAB hPrefix hMiddle hPost hFirst hSecond
  refine ⟨c, hc, ?_, hCross⟩
  exact Kyprianou.Ch01.twoPieceOccupationBeforeFirstLePhysicalTime
    X ω y j hy t a b ha hAB hPrefix hMiddle hPost hFirst hSecond
