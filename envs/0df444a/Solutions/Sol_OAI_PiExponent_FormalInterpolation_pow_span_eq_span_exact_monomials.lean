-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.pow_span_eq_span_exact_monomials
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:12:20.231405+00:00
-- url     : https://prove2.me/submissions/b326b3c1-e21c-4287-b60b-2a8ed9e2db0e

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]
    (f : σ → R) (n : Nat) :
    (Ideal.span (Set.range f)) ^ n =
      Ideal.span {x : R | ∃ b : σ → Nat, (∑ i, b i) = n ∧ x = ∏ i, f i ^ (b i)} := by
  classical
  have hset :
      (fun b : σ →₀ Nat => b.prod (fun i k => f i ^ k)) ''
          {b | b.degree = n ∧ (b.support : Set σ) ⊆ Set.univ} =
        {x : R | ∃ b : σ → Nat, (∑ i, b i) = n ∧ x = ∏ i, f i ^ (b i)} := by
    ext x
    constructor
    · rintro ⟨b, ⟨hb, hs⟩, rfl⟩
      refine ⟨Finsupp.equivFunOnFinite b, ?_, ?_⟩
      · simpa [Finsupp.degree_eq_sum] using hb
      · simp [Finsupp.prod_fintype, Finsupp.equivFunOnFinite]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Finsupp.equivFunOnFinite.symm b, ?_, ?_⟩
      · simpa [Finsupp.degree_eq_sum] using hb
      · simp [Finsupp.prod_fintype, Finsupp.equivFunOnFinite]
  rw [Ideal.span, Submodule.span_pow, ← Set.image_univ,
    Finsupp.image_pow_eq_finsuppProd_image, hset]