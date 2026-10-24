-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_finite_homogeneous_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:43:06.082039+00:00
-- url     : https://prove2.me/submissions/0e10e965-984d-4942-b8f1-e987033f5eb4

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_in_homogeneous_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_coordinate_power_relations

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (hfinite : Module.Finite Complex ((MvPolynomial (Fin d) Complex) ⧸ J)) :
    Module.Finite (Algebra.adjoin Complex (Set.range g)) (MvPolynomial (Fin d) Complex) := by
  have hpowers : ∀ i, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n ∈ J :=
    OAI.PiExponent.FormalInterpolation.coordinate_powers_in_homogeneous_ideal
      w hw D hD g hhom J hspan hfinite
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_power_relations
    w hw D hD g hhom J hspan hpowers