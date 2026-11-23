-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorCumulantEqOfCommonGenerator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:18:07.734921+00:00
-- url     : https://prove2.me/submissions/c70854c8-9cf2-4c37-956f-7f9fa6c02034

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingMechanismLocallyLipschitzPositive
import Theorems.Thm_Kyprianou_Ch01_branchingCumulantODEUniqueOfLocallyLipschitzMechanism
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
        branchingLaplace K₂ 1 t q < 1) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingU K₁ t q = branchingU K₂ t q := by
  have hLip :=
    Kyprianou.Ch01.branchingMechanismLocallyLipschitzPositive
      (rate : ℝ) offspring
  exact Kyprianou.Ch01.branchingCumulantODEUniqueOfLocallyLipschitzMechanism
    rate hrate offspring hNoZeroJumps K₁ K₂ hBranch₁ hBranch₂
    hSemi₁ hSemi₂ hInit₁ hInit₂ hGen₁ hGen₂
    hPos₁ hPos₂ hBelow₁ hBelow₂ hLip
