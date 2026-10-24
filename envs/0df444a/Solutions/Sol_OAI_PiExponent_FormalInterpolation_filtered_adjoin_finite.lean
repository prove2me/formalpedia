-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.filtered_adjoin_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:30:04.940646+00:00
-- url     : https://prove2.me/submissions/a616cedf-a3ef-4d47-8c48-185ad2717f82

import Mathlib
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_filtered_adjoin_finite_integral_variables
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_of_integral_variables

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
            (fun k : Fin d => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex)) :
    Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  let A := Algebra.adjoin Complex (Set.range g)
  apply OAI.PiExponent.FormalInterpolation.finite_of_integral_variables A
  intro i
  exact OAI.PiExponent.FormalInterpolation.filtered_adjoin_finite_integral_variables
    w hw D hD m g hbound hfinite i