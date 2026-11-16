-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_evolution_left_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:03:26.065213+00:00
-- url     : https://prove2.me/submissions/9ca92abd-5db3-4d2a-8da7-c16dc781df22

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_timeContinuous
import Theorems.Thm_Kyprianou_Ch01_branchingU_vectorFieldContinuous
import Theorems.Thm_Kyprianou_Ch01_branchingU_leftDerivative_of_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

/-- Reduce the left branching derivative to nontrivial cumulant and mechanism continuity. -/
theorem solution
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Iic (t : ℝ)) (t : ℝ) := by
  have hUcont :=
    Kyprianou.Ch01.branchingU_timeContinuous law rate offspring
      hbranch hsemigroup hinit hpositive hgenerator q hq
  have hGcont :=
    Kyprianou.Ch01.branchingU_vectorFieldContinuous law rate offspring
      hbranch hsemigroup hinit hpositive hgenerator q hq hUcont
  exact Kyprianou.Ch01.branchingU_leftDerivative_of_continuity
    law rate offspring hbranch hsemigroup hinit hpositive hgenerator
    q hq t ht hUcont hGcont
