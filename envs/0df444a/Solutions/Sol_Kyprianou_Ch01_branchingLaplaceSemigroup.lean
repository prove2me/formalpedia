-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplaceSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:35:06.941201+00:00
-- url     : https://prove2.me/submissions/6a632665-7214-4e64-af4c-5fcc87cbcf29

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceMarkovFactorization
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hmarkov : IsPopulationMarkovSemigroup law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi ∧
        branchingLaplace law 1 t phi < 1) :
    ∀ (s t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingU law (s + t) phi =
        branchingU law s (branchingU law t phi)  := by
  intro s t phi hphi
  have h := Kyprianou.Ch01.branchingLaplaceMarkovFactorization
    law hbranch hmarkov hzero hpositive s t phi hphi
  exact congrArg (fun u : ℝ => -Real.log u) h
