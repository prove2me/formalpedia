-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorLaplaceEqPositiveRate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:58:05.644876+00:00
-- url     : https://prove2.me/submissions/ff6f777b-72b9-44ca-8281-1409675ecc0c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceBelowOnePositiveRate
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
        0 < branchingLaplace K₂ 1 t q) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingLaplace K₁ 1 t q = branchingLaplace K₂ 1 t q := by
  have hBelow₁ :=
    Kyprianou.Ch01.branchingOneAncestorLaplaceBelowOnePositiveRate
      rate hrate offspring K₁ hSemi₁ hInit₁ hGen₁
  have hBelow₂ :=
    Kyprianou.Ch01.branchingOneAncestorLaplaceBelowOnePositiveRate
      rate hrate offspring K₂ hSemi₂ hInit₂ hGen₂
  have hU :=
    Kyprianou.Ch01.branchingOneAncestorCumulantEqOfCommonGenerator
      rate hrate offspring hNoZeroJumps K₁ K₂
      hBranch₁ hBranch₂ hSemi₁ hSemi₂ hInit₁ hInit₂
      hGen₁ hGen₂ hPos₁ hPos₂ hBelow₁ hBelow₂
  intro t q hq
  have hc : -Real.log (branchingLaplace K₁ 1 t q) =
      -Real.log (branchingLaplace K₂ 1 t q) := by
    simpa only [branchingU] using hU t q hq
  have hlog : Real.log (branchingLaplace K₁ 1 t q) =
      Real.log (branchingLaplace K₂ 1 t q) := neg_inj.mp hc
  have hExp := congrArg Real.exp hlog
  simpa only [Real.exp_log (hPos₁ t q hq),
    Real.exp_log (hPos₂ t q hq)] using hExp
