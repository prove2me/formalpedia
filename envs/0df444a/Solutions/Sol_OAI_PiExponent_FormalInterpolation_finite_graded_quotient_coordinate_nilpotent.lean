-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_graded_quotient_coordinate_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:04:36.007551+00:00
-- url     : https://prove2.me/submissions/ca67968d-02f2-4029-9979-81dee5dbca4c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_coordinate_integral_relation_v3
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_relation_implies_coordinate_nilpotent_v3

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hcomponents : ∀ f : MvPolynomial (Fin d) ℂ, f ∈ I →
      ∀ r : ℚ,
        MvPolynomial.weightedHomogeneousComponent w r f ∈ I)
    (hquot : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I)) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by
  intro i
  obtain ⟨p, hp, hpI⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_integral_relation_v3
      I hquot i
  exact
    OAI.PiExponent.FormalInterpolation.homogeneous_relation_implies_coordinate_nilpotent_v3
      w hw I hcomponents i p hp hpI