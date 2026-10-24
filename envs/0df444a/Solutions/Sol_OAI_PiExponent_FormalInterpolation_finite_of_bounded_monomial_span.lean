-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_of_bounded_monomial_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:36:08.949602+00:00
-- url     : https://prove2.me/submissions/c08d0df1-2dde-4cbf-8eaf-913e5b0892fd

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_monomials_finite
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_of_monomials_in_span

open scoped BigOperators

theorem solution {d : Nat} (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ) (n : Fin d → Nat)
    (hspan : ∀ e : Fin d →₀ Nat,
      MvPolynomial.monomial e (1 : ℂ) ∈
        Submodule.span (Algebra.adjoin ℂ (Set.range p))
          {f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧
              f = MvPolynomial.monomial a (1 : ℂ)}) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p))
      (MvPolynomial (Fin d) ℂ) := by
  exact OAI.PiExponent.FormalInterpolation.finite_of_monomials_in_span
    (A := Algebra.adjoin ℂ (Set.range p))
    (S := {f : MvPolynomial (Fin d) ℂ |
      ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧
        f = MvPolynomial.monomial a (1 : ℂ)})
    (OAI.PiExponent.FormalInterpolation.bounded_monomials_finite n)
    hspan