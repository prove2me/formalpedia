-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_filtered_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:20:45.031165+00:00
-- url     : https://prove2.me/submissions/84a94c95-7138-4967-a4d8-53edb2a5192f

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_filtered_lifts_coordinates_integral_repair6
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_of_integral_coordinates_over_repair6
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hbound : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hfinite : Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex)) :
    Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  apply OAI.PiExponent.FormalInterpolation.finite_of_integral_coordinates_over_repair6
  intro i
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_of_filtered_lifts_coordinates_integral_repair6
    w hw D hD m g hbound hfinite i