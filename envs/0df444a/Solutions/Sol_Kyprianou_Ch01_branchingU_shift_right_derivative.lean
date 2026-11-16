-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_shift_right_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:54:29.853401+00:00
-- url     : https://prove2.me/submissions/b8061f47-720d-4cc3-92d2-9e1bd5bccc66

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingZeroAbsorbing
import Theorems.Thm_Kyprianou_Ch01_branchingU_derivativeAtZero
import Theorems.Thm_Kyprianou_Ch01_branchingU_positive
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceSemigroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

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
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) :
    HasDerivWithinAt
      (fun u : ℝ => branchingU law (t + Real.toNNReal u) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Ici 0) 0 := by
  have hp : 0 < branchingU law t q :=
    Kyprianou.Ch01.branchingU_positive law hpositive t q hq
  have h0 := Kyprianou.Ch01.branchingU_derivativeAtZero
    law rate offspring hinit hgenerator (branchingU law t q) hp
  apply h0.congr_of_eventuallyEq_of_mem ?_ (by simp)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have habs : ∀ t : ℝ≥0, law 0 t = PMF.pure 0 :=
    Kyprianou.Ch01.branchingZeroAbsorbing law hbranch
  have h := Kyprianou.Ch01.branchingLaplaceSemigroup
    law hbranch hsemigroup habs hpositive
    (Real.toNNReal u) t q hq
  simpa only [add_comm] using h
