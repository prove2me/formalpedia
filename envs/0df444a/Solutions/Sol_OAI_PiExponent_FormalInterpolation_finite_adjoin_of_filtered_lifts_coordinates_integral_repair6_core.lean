-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_filtered_lifts_coordinates_integral_repair6_core
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:52:35.451983+00:00
-- url     : https://prove2.me/submissions/f3961afc-946d-4d93-81c0-30378ae3330e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_top_components_coordinates_integral_repair7
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_finite_of_integral_coordinates_repair7

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
    Module.Finite
      (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  apply OAI.PiExponent.FormalInterpolation.mvPolynomial_finite_of_integral_coordinates_repair7
  intro i
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_of_top_components_coordinates_integral_repair7
    w hw D hD m g hbound hfinite i