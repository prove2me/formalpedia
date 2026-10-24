-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_top_components_coordinates_integral_repair7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:01:03.851609+00:00
-- url     : https://prove2.me/submissions/aa0830cc-0192-4f0b-810f-fd8f509d1a4f

import Mathlib
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_filtered_adjoin_finite
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_coordinates_integral

open scoped BigOperators

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
    ∀ i : Fin d,
      IsIntegral
        (Algebra.adjoin Complex (Set.range g))
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) := by
  have hB : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) :=
    OAI.PiExponent.FormalInterpolation.filtered_adjoin_finite
      w hw D hD m g hbound hfinite
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_coordinates_integral
    (d := d) (g := g) hB