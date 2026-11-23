-- Prove2me | solution 2 for Kyprianou.Ch01.branchingCumulantODEUniqueOfLocallyLipschitzMechanism
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:40:38.48552+00:00
-- url     : https://prove2.me/submissions/078f3499-7c58-49d5-9267-637a2ade07cd

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingCumulantFiniteHorizonRegular
import Theorems.Thm_Kyprianou_Ch01_positiveContinuousPairCommonCompactBounds
import Theorems.Thm_Kyprianou_Ch01_autonomousODEUniqueWithCompactPositiveRange
import Theorems.Thm_Kyprianou_Ch01_branchingU_zero
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
  intro T q hq
  let f : ℝ → ℝ := fun s => branchingU K₁ (Real.toNNReal s) q
  let g : ℝ → ℝ := fun s => branchingU K₂ (Real.toNNReal s) q
  have hf := Kyprianou.Ch01.branchingCumulantFiniteHorizonRegular
    rate hrate offspring hNoZeroJumps K₁ hBranch₁ hSemi₁ hInit₁
    hGen₁ hPos₁ hBelow₁ T q hq
  have hg := Kyprianou.Ch01.branchingCumulantFiniteHorizonRegular
    rate hrate offspring hNoZeroJumps K₂ hBranch₂ hSemi₂ hInit₂
    hGen₂ hPos₂ hBelow₂ T q hq
  obtain ⟨δ, B, hδ, hδB, hRange⟩ :=
    Kyprianou.Ch01.positiveContinuousPairCommonCompactBounds
      f g (T : ℝ) T.property hf.1 hg.1 hf.2.1 hg.2.1
  obtain ⟨C, hC, hLC⟩ := hLip δ B hδ hδB
  have hInit : f 0 = g 0 := by
    have hf0 := Kyprianou.Ch01.branchingU_zero K₁ hInit₁ q
    have hg0 := Kyprianou.Ch01.branchingU_zero K₂ hInit₂ q
    simpa [f, g] using hf0.trans hg0.symm
  have hEq := Kyprianou.Ch01.autonomousODEUniqueWithCompactPositiveRange
    (branchingMechanism (rate : ℝ) offspring)
    δ B C hδ hδB hC hLC f g (T : ℝ) T.property
    hf.1 hg.1 (fun s hs => (hRange s hs).1)
    (fun s hs => (hRange s hs).2)
    hf.2.2 hg.2.2 hInit
  simpa [f, g] using hEq
