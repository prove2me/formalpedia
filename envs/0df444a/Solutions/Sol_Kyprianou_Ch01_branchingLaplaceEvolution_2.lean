-- Prove2me | solution 2 for Kyprianou.Ch01.branchingLaplaceEvolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:48:42.558354+00:00
-- url     : https://prove2.me/submissions/0401eb60-c7f9-4aee-82b8-947961a07ac3

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_zero
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Exercise 1.11(iii) reduces to the proved initial cumulant and the
    full relative-time branching evolution derivative. -/
theorem solution
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hrate : 0 < rate)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ =>
          branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0) :
    ∀ q : ℝ, 0 < q →
      branchingU law 0 q = q ∧
      ∀ t : ℝ≥0,
        HasDerivWithinAt
          (fun s : ℝ => branchingU law (Real.toNNReal s) q)
          (branchingMechanism rate offspring (branchingU law t q))
          (Set.Ici 0) (t : ℝ) := by
  intro q hq
  exact ⟨Kyprianou.Ch01.branchingU_zero law hinit q,
    Kyprianou.Ch01.branchingU_evolution_derivative law rate offspring
      hrate hbranch hsemigroup hinit hpositive hgenerator q hq⟩
