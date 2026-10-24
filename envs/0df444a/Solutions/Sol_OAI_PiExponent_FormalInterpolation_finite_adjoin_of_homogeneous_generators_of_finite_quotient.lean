-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_generators_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:51:34.472977+00:00
-- url     : https://prove2.me/submissions/5ee95a34-65bb-4601-8681-83c5572e774f

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_of_finite_homogeneous_quotient
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_coordinate_powers
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))] :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  apply OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_powers w hw D hD m p hp
  exact OAI.PiExponent.FormalInterpolation.coordinate_powers_of_finite_homogeneous_quotient
    w hw D hD m p hp