-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_leftDerivative_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:58:46.270199+00:00
-- url     : https://prove2.me/submissions/23fd54f4-2172-4f39-8c35-5e51e7c80b76

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingU_evolution_right_derivative
import Theorems.Thm_Kyprianou_Ch01_continuousRightDerivative_impliesLeft

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

/-- Branching evolution left derivative follows from time continuity and the right derivative. -/
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
    (q : ℝ) (hq : 0 < q) (t : ℝ≥0) (ht : 0 < t)
    (hUcont : ContinuousOn
      (fun s : ℝ => branchingU law (Real.toNNReal s) q) (Set.Ici 0))
    (hGcont : Continuous
      (fun s : ℝ =>
        branchingMechanism rate offspring
          (branchingU law (Real.toNNReal s) q))) :
    HasDerivWithinAt
      (fun s : ℝ => branchingU law (Real.toNNReal s) q)
      (branchingMechanism rate offspring (branchingU law t q))
      (Set.Iic (t : ℝ)) (t : ℝ) := by
  let f : ℝ → ℝ := fun s => branchingU law (Real.toNNReal s) q
  let g : ℝ → ℝ := fun s =>
    branchingMechanism rate offspring (branchingU law (Real.toNNReal s) q)
  have hright (x : ℝ) (hx : 0 ≤ x) :
      HasDerivWithinAt f (g x) (Ioi x) x := by
    have hr := Kyprianou.Ch01.branchingU_evolution_right_derivative
      law rate offspring hbranch hsemigroup hinit hpositive hgenerator
      q hq (Real.toNNReal x)
    have hxcoe : ((Real.toNNReal x : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx
    dsimp [f, g]
    simpa only [hxcoe] using hr.mono Ioi_subset_Ici_self
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hleft :=
    Kyprianou.Ch01.continuousRightDerivative_impliesLeft
      f g hUcont hGcont hright (t : ℝ) htR
  simpa only [f, g, Real.toNNReal_coe] using hleft
