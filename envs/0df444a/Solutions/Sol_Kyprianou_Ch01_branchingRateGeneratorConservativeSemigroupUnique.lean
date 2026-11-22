-- Prove2me | solution 1 for Kyprianou.Ch01.branchingRateGeneratorConservativeSemigroupUnique
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:37:11.714832+00:00
-- url     : https://prove2.me/submissions/29ad453d-7bd4-4546-93d4-d24474d4f44e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingSemigroupEqOfOneAncestor
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLawEqOfMatchingGenerator
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniqueness of the one-ancestor transition law implies uniqueness
of the entire conservative branching transition semigroup. -/
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
    (hGen₂ : IsBranchingRateGenerator K₂ rate offspring) :
    K₁ = K₂ := by
  have hOne : ∀ t : ℝ≥0, K₁ 1 t = K₂ 1 t :=
    Kyprianou.Ch01.branchingOneAncestorLawEqOfMatchingGenerator
      rate offspring hNoZeroJumps K₁ K₂
      hBranch₁ hBranch₂ hSemi₁ hSemi₂
      hInit₁ hInit₂ hGen₁ hGen₂
  exact Kyprianou.Ch01.branchingSemigroupEqOfOneAncestor
    K₁ K₂ hBranch₁ hBranch₂ hOne
