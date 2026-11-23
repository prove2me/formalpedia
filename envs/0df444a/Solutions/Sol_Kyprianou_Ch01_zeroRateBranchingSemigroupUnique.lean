-- Prove2me | solution 1 for Kyprianou.Ch01.zeroRateBranchingSemigroupUnique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:47:20.570868+00:00
-- url     : https://prove2.me/submissions/aef970fd-840e-419c-b348-bf19a3f9f04a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_lampertiLatticeGeneratorSemigroupUnique
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ y : ℕ, K₁ y 0 = PMF.pure y)
    (hInit₂ : ∀ y : ℕ, K₂ y 0 = PMF.pure y)
    (hGen₁ : IsBranchingRateGenerator K₁ 0 offspring)
    (hGen₂ : IsBranchingRateGenerator K₂ 0 offspring) :
    K₁ = K₂ := by
  apply Kyprianou.Ch01.lampertiLatticeGeneratorSemigroupUnique
    (0 : ℝ≥0) offspring hNoZeroJumps K₁ K₂
    hSemi₁ hSemi₂ hInit₁ hInit₂
  · intro y k
    simpa [IsBranchingRateGenerator] using (hGen₁ y k)
  · intro y k
    simpa [IsBranchingRateGenerator] using (hGen₂ y k)
