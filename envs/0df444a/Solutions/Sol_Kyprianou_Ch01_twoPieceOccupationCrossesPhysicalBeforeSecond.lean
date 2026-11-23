-- Prove2me | solution 1 for Kyprianou.Ch01.twoPieceOccupationCrossesPhysicalBeforeSecond
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:56:49.274531+00:00
-- url     : https://prove2.me/submissions/abd8dfc9-b4aa-4ff6-9fde-ffbe83361049

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_twoPiecePostJumpIntervalOccupationLower
import Theorems.Thm_Kyprianou_Ch01_twoPiecePositiveRatioStrict
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
      (t : ℝ≥0∞) < reciprocalOccupation X c ω := by
  have ht : 0 < t := by
    by_contra hn
    have hz : t = 0 := le_antisymm (le_of_not_gt hn) t.property
    simp [hz] at hFirst
    linarith
  have hRatio :=
    Kyprianou.Ch01.twoPiecePositiveRatioStrict
      X ω y j hy t a b ha hAB hPrefix hMiddle hPost hFirst hSecond ht
  have hIntegral :=
    Kyprianou.Ch01.twoPiecePostJumpIntervalOccupationLower
      X ω y j hy t a b ha hAB hPrefix hMiddle hPost hFirst hSecond
  let c : ℝ≥0 := Real.toNNReal
    (a + ((y + j : ℕ) : ℝ) * (t : ℝ))
  have hcNonneg : 0 ≤ a + ((y + j : ℕ) : ℝ) * (t : ℝ) := by
    have hn : 0 ≤ ((y + j : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht0 : 0 ≤ (t : ℝ) := t.property
    nlinarith [ha]
  refine ⟨c, ?_, ?_⟩
  · change (Real.toNNReal
      (a + ((y + j : ℕ) : ℝ) * (t : ℝ)) : ℝ) < b
    rw [Real.coe_toNNReal _ hcNonneg]
    exact hSecond
  · exact hRatio.trans_le hIntegral
