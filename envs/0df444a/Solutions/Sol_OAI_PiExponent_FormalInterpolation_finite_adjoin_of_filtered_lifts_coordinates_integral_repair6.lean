-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_filtered_lifts_coordinates_integral_repair6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:41:51.166547+00:00
-- url     : https://prove2.me/submissions/cdfd496d-8fdf-4e9a-ba41-a9427bead414
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_integral_of_finite_adjoin_weighted_components
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_integral_of_filtered_lift_of_integral_weighted_components

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
      (MvPolynomial (Fin d) Complex))
    (i : Fin d) :
    IsIntegral (Algebra.adjoin Complex (Set.range g) :
      Subalgebra Complex (MvPolynomial (Fin d) Complex))
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) := by
  apply OAI.PiExponent.FormalInterpolation.integral_of_filtered_lift_of_integral_weighted_components
    w hw D hD m g hbound i
  exact OAI.PiExponent.FormalInterpolation.integral_of_finite_adjoin_weighted_components
    w D m g hfinite i