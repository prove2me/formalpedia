-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_span_pow_mem_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:01:29.139481+00:00
-- url     : https://prove2.me/submissions/cd875580-ebb8-4f20-8cb1-33e7f08421b9

import Mathlib.RingTheory.MvPolynomial.Ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_pow_span_eq_span_exact_monomials
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_span_exact_monomials_mem_expansion

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]
    (f : σ → R) (n : Nat) (p : R)
    (hp : p ∈ (Ideal.span (Set.range f)) ^ n) :
    ∃ (m : Nat) (b : Fin m → σ → Nat) (q : Fin m → R),
      (∀ j, (∑ i, b j i) = n) ∧
      p = ∑ j, (∏ i, f i ^ (b j i)) * q j := by
  have hspan := OAI.PiExponent.FormalInterpolation.pow_span_eq_span_exact_monomials f n
  rw [hspan] at hp
  exact OAI.PiExponent.FormalInterpolation.span_exact_monomials_mem_expansion f n p hp