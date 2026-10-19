-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.variablePowerIdeal_pow_mem_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:54:43.026675+00:00
-- url     : https://prove2.me/submissions/38158356-16f7-4230-918f-c462998f8869

import Mathlib.RingTheory.MvPolynomial.Ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_span_pow_mem_expansion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePower_product_eq_monomial

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e : σ → Nat) (n : Nat) (p : MvPolynomial σ k)
    (hp : p ∈ (Ideal.span (Set.range
      (fun i : σ => (MvPolynomial.X i : MvPolynomial σ k) ^ e i))) ^ n) :
    ∃ (m : Nat) (b : Fin m → σ → Nat)
      (q : Fin m → MvPolynomial σ k),
      (∀ j, (∑ i, b j i) = n) ∧
      p = ∑ j, MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b j i)) (1 : k) * q j := by
  obtain ⟨m, b, q, hb, hp'⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_span_pow_mem_expansion
      (f := fun i : σ => (MvPolynomial.X i : MvPolynomial σ k) ^ e i) n p hp
  refine ⟨m, b, q, hb, ?_⟩
  simpa only [OAI.PiExponent.FormalInterpolation.variablePower_product_eq_monomial] using hp'