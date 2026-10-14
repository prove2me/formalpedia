-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.pow_eq_span_fin_products
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T19:04:16.369843+00:00
-- url     : https://prove2.me/submissions/d432503e-293e-4c0b-b8c3-2c93b1bac365

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem solution
    {A : Type*} [CommSemiring A] (I : Ideal A) (n : ℕ) :
    I ^ n = Ideal.span
      {x : A | ∃ f : Fin n → A, (∀ i, f i ∈ I) ∧ x = ∏ i, f i} := by
  rw [Submodule.pow_eq_span_pow_set]
  congr 1
  ext x
  rw [Set.mem_pow_iff_prod]
  constructor
  · rintro ⟨f, hf, hprod⟩
    exact ⟨f, hf, hprod.symm⟩
  · rintro ⟨f, hf, hprod⟩
    exact ⟨f, hf, hprod.symm⟩
