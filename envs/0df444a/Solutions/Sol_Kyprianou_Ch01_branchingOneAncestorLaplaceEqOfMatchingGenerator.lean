-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorLaplaceEqOfMatchingGenerator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:51:38.903205+00:00
-- url     : https://prove2.me/submissions/34dc55f5-fc08-44b2-bf9e-8e03929839d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_zeroRateBranchingSemigroupUnique
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceEqPositiveRate
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (offspring : PMF ℕ)
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
        0 < branchingLaplace K₂ 1 t q) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingLaplace K₁ 1 t q = branchingLaplace K₂ 1 t q := by
  by_cases hzero : rate = 0
  · have hGenZ₁ : IsBranchingRateGenerator K₁ 0 offspring := by
      simpa [hzero] using hGen₁
    have hGenZ₂ : IsBranchingRateGenerator K₂ 0 offspring := by
      simpa [hzero] using hGen₂
    have heq : K₁ = K₂ :=
      Kyprianou.Ch01.zeroRateBranchingSemigroupUnique
        offspring hNoZeroJumps K₁ K₂
        hSemi₁ hSemi₂ hInit₁ hInit₂ hGenZ₁ hGenZ₂
    intro t q hq
    rw [← heq]
  · have hrate : 0 < rate :=
      lt_of_le_of_ne (show (0 : ℝ≥0) ≤ rate from zero_le) (Ne.symm hzero)
    exact Kyprianou.Ch01.branchingOneAncestorLaplaceEqPositiveRate
      rate hrate offspring hNoZeroJumps K₁ K₂
      hBranch₁ hBranch₂ hSemi₁ hSemi₂
      hInit₁ hInit₂ hGen₁ hGen₂ hPos₁ hPos₂
