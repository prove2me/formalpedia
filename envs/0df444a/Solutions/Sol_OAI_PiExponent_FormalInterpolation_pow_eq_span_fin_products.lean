-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.pow_eq_span_fin_products
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:13:20.232817+00:00
-- url     : https://prove2.me/submissions/710d25bd-607d-4ab3-ba35-f3d832faf7c3

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem solution {α : Type*} [CommSemiring α] (I : Ideal α) (n : ℕ) :
    I ^ n = Ideal.span {P : α | ∃ s : Fin n → α, (∀ i, s i ∈ I) ∧ P = ∏ i, s i} := by
  rw [Submodule.pow_eq_span_pow_set]
  congr 1
  ext P
  simp only [Set.mem_pow_iff_prod, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, hprod⟩
    exact ⟨s, hs, hprod.symm⟩
  · rintro ⟨s, hs, hprod⟩
    exact ⟨s, hs, hprod.symm⟩