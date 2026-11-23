-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorLawEqOfMatchingGenerator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:17:27.499317+00:00
-- url     : https://prove2.me/submissions/fb97597c-bd75-4b9e-b126-b0b223139a09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceStrictPositive
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceEqOfMatchingGenerator
import Theorems.Thm_Kyprianou_Ch01_pmfNatLaplaceEq
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
    (hGen₂ : IsBranchingRateGenerator K₂ rate offspring) :
    ∀ t : ℝ≥0, K₁ 1 t = K₂ 1 t := by
  have hPos₁ :=
    Kyprianou.Ch01.branchingOneAncestorLaplaceStrictPositive K₁
  have hPos₂ :=
    Kyprianou.Ch01.branchingOneAncestorLaplaceStrictPositive K₂
  have hEq :=
    Kyprianou.Ch01.branchingOneAncestorLaplaceEqOfMatchingGenerator
      rate offspring hNoZeroJumps K₁ K₂ hBranch₁ hBranch₂
      hSemi₁ hSemi₂ hInit₁ hInit₂ hGen₁ hGen₂ hPos₁ hPos₂
  intro t
  apply Kyprianou.Ch01.pmfNatLaplaceEq
  intro q hq
  exact hEq t q hq
