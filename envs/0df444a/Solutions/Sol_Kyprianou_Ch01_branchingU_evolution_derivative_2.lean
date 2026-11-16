-- Prove2me | solution 2 for Kyprianou.Ch01.branchingU_evolution_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:47:52.477704+00:00
-- url     : https://prove2.me/submissions/1e04f7be-575d-4e3d-91ce-2666a77f6433

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_right_derivative
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_left_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- The full half-line evolution derivative follows from the two
    published one-sided derivative obligations at positive times. -/
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
      ∀ t : ℝ≥0,
        HasDerivWithinAt
          (fun s : ℝ => branchingU law (Real.toNNReal s) q)
          (branchingMechanism rate offspring (branchingU law t q))
          (Set.Ici 0) (t : ℝ) := by
  intro q hq t
  by_cases ht : t = 0
  · subst t
    simpa only [NNReal.coe_zero] using
      (Kyprianou.Ch01.branchingU_evolution_right_derivative
        law rate offspring hbranch hsemigroup hinit hpositive hgenerator
        q hq (0 : ℝ≥0))
  · have htpos : 0 < t := (pos_iff_ne_zero).2 ht
    have hl := Kyprianou.Ch01.branchingU_evolution_left_derivative
      law rate offspring hbranch hsemigroup hinit hpositive hgenerator
      q hq t htpos
    have hr := Kyprianou.Ch01.branchingU_evolution_right_derivative
      law rate offspring hbranch hsemigroup hinit hpositive hgenerator
      q hq t
    have hall := hl.union hr
    rw [Iic_union_Ici] at hall
    exact hall.mono (Set.subset_univ _)
