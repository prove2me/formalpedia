-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_evolution_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:54:11.567207+00:00
-- url     : https://prove2.me/submissions/d9911120-4059-4e3f-a607-c1130da2f465

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_zero
import Theorems.Thm_Kyprianou_Ch01_branchingU_derivativeAtZero
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_left_derivative
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_right_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- The zero-time identity and the matching one-sided derivatives yield the evolution law. -/
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
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
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
    have h0 := Kyprianou.Ch01.branchingU_derivativeAtZero
      law rate offspring hinit hgenerator q hq
    have hu0 := Kyprianou.Ch01.branchingU_zero law hinit q
    simpa [hu0] using h0
  · have htpos : 0 < t := lt_of_le_of_ne (bot_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
    have hleft := Kyprianou.Ch01.branchingU_evolution_left_derivative
      law rate offspring hbranch hsemigroup hinit hpositive
      hgenerator q hq t htpos
    have hright := Kyprianou.Ch01.branchingU_evolution_right_derivative
      law rate offspring hbranch hsemigroup hinit hpositive
      hgenerator q hq t
    have hcover : Set.Iic (t : ℝ) ∪ Set.Ici (t : ℝ) = Set.univ := by
      ext s
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici,
        Set.mem_univ, iff_true]
      exact le_total s (t : ℝ)
    have hderiv := (hleft.union hright).hasDerivAt (by simp [hcover])
    exact hderiv.hasDerivWithinAt
