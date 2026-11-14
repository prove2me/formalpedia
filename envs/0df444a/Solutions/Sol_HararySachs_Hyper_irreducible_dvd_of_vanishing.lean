-- Prove2me | solution 1 for HararySachs.Hyper.irreducible_dvd_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T22:14:28.613242+00:00
-- url     : https://prove2.me/submissions/f57d945f-1aff-4d26-8123-2b68464a7436

import Mathlib

open MvPolynomial

theorem solution {σ : Type*} [Fintype σ] (g f : MvPolynomial σ ℂ)
    (hg : Irreducible g)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x g = 0 → MvPolynomial.eval x f = 0) : g ∣ f := by
  classical
  have hprime : (Ideal.span {g}).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr hg.prime
  have key : f ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span {g})) := by
    rw [mem_vanishingIdeal_iff]
    intro u hu
    rw [mem_zeroLocus_iff] at hu
    have hgu : aeval u g = 0 := hu g (Ideal.subset_span rfl)
    exact h u hgu
  rw [IsPrime.vanishingIdeal_zeroLocus] at key
  exact Ideal.mem_span_singleton.mp key
