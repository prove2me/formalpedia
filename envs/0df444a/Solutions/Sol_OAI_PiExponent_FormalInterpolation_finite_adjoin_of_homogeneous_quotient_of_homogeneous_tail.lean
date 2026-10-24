-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_quotient_of_homogeneous_tail
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:27:24.128335+00:00
-- url     : https://prove2.me/submissions/03fc0400-6fe8-47b2-b1d2-b5a444a482c8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_monomial_tail

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (B : ℚ)
    (hB : ∀ (t : ℚ) (f : MvPolynomial (Fin d) ℂ),
      B < t → MvPolynomial.IsWeightedHomogeneous w f t → f ∈ Ideal.span (Set.range p)) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  apply OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_monomial_tail
    (w := w) (hw := hw) (D := D) (hD := hD) (m := m) (p := p) (hp := hp) (B := B)
  intro e t ht he
  exact hB t (MvPolynomial.monomial e (1 : ℂ)) ht he