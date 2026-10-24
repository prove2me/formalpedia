-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_weighted_homogeneous_top_components
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:11:21.157139+00:00
-- url     : https://prove2.me/submissions/ff912add-52b0-48b5-a1cc-e3ddb95d5574

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_coordinate_power_relations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_coefficients_of_span_coordinate_power

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (htop : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      MvPolynomial.X i ^ N ∈ Ideal.span
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j)))) :
    Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex) := by
  let p : Fin m → MvPolynomial (Fin d) Complex := fun j =>
    MvPolynomial.weightedHomogeneousComponent
      (fun k => (w k : ℚ)) (D : ℚ) (g j)
  have hp : ∀ j, MvPolynomial.IsWeightedHomogeneous
      (fun k => (w k : ℚ)) (p j) (D : ℚ) := by
    intro j
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := fun k => (w k : ℚ)) (n := (D : ℚ)) (φ := g j)
  apply OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_coordinate_power_relations
    (w := fun k => (w k : ℚ)) (hw := hw) (D := D) (hD := hD)
    (m := m) (p := p) (hp := hp)
  intro i
  obtain ⟨N, hN, hmem⟩ := htop i
  obtain ⟨c, hc, hrel⟩ :=
    OAI.PiExponent.FormalInterpolation.homogeneous_coefficients_of_span_coordinate_power
      (w := fun k => (w k : ℚ)) (D := D) (m := m) (p := p) (hp := hp)
      i N hN hmem
  exact ⟨N, hN, c, hc, hrel⟩