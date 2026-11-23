-- Prove2me | solution 1 for Kyprianou.Ch01.branchingCumulantODEUniqueOfLocallyLipschitzMechanism
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T09:39:55.021095+00:00
-- url     : https://prove2.me/submissions/67b3f177-74be-43fa-99aa-f851a752aaa0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorCumulantEqOfCommonGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (hNoZeroJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hBranch₁ : HasBranchingProperty K₁)
    (hBranch₂ : HasBranchingProperty K₂)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ y : ℕ, K₁ y 0 = PMF.pure y)
    (hInit₂ : ∀ y : ℕ, K₂ y 0 = PMF.pure y)
    (hGen₁ : IsBranchingRateGenerator K₁ rate offspring)
    (hGen₂ : IsBranchingRateGenerator K₂ rate offspring)
    (hPos₁ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        0 < branchingLaplace K₁ 1 t q)
    (hPos₂ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        0 < branchingLaplace K₂ 1 t q)
    (hBelow₁ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        branchingLaplace K₁ 1 t q < 1)
    (hBelow₂ : ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
        branchingLaplace K₂ 1 t q < 1)
    (hLip : ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |branchingMechanism (rate : ℝ) offspring y -
            branchingMechanism (rate : ℝ) offspring x| ≤
            C * |y - x|) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingU K₁ t q = branchingU K₂ t q := by
  exact Kyprianou.Ch01.branchingOneAncestorCumulantEqOfCommonGenerator
    rate hrate offspring hNoZeroJumps K₁ K₂ hBranch₁ hBranch₂ hSemi₁ hSemi₂
    hInit₁ hInit₂ hGen₁ hGen₂ hPos₁ hPos₂ hBelow₁ hBelow₂
