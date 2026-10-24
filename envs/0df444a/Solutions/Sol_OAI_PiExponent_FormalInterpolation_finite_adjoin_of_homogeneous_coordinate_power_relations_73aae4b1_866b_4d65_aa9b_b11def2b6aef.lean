-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_coordinate_power_relations_73aae4b1_866b_4d65_aa9b_b11def2b6aef
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:46:20.020071+00:00
-- url     : https://prove2.me/submissions/34900e54-15db-4049-ad76-792e6fececa5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_coordinate_power_relations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_generators_of_finite_quotient

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (N : Nat) (hN : 0 < N)
    (hpow : ∀ i : Fin d,
      MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ) ∈ Ideal.span (Set.range p)) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  letI : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p)) :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_power_relations
      (m := m) (p := p) (N := N) hpow
  exact
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_generators_of_finite_quotient
      (w := w) (hw := hw) (D := D) (hD := hD) (m := m) (p := p) (hp := hp)