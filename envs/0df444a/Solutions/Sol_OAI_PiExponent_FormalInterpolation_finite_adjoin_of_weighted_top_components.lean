-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_weighted_top_components
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:56:09.825911+00:00
-- url     : https://prove2.me/submissions/b10cde6c-d520-4b9d-84cb-b2d409631a7a

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_weighted_homogeneous_top_components
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_filtered_lifts

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hbound : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (htop : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      MvPolynomial.X i ^ N ∈ Ideal.span
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j)))) :
    Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  have hfinite :
      Module.Finite
        (Algebra.adjoin Complex
          (Set.range (fun j =>
            MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j))))
        (MvPolynomial (Fin d) Complex) :=
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_weighted_homogeneous_top_components
      w hw D hD m g htop
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_of_filtered_lifts
    w hw D hD m g hbound hfinite