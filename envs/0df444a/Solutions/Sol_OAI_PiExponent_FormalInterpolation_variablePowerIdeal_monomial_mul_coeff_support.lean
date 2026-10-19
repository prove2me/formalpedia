-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.variablePowerIdeal_monomial_mul_coeff_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:46:11.233947+00:00
-- url     : https://prove2.me/submissions/f1eaa8a5-f80b-4982-ba8c-856ecf12ea53

import Mathlib.RingTheory.MvPolynomial.Ideal

theorem solution
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e : σ → Nat) (b : σ → Nat) (q : MvPolynomial σ k)
    (d : σ →₀ Nat)
    (h : (MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i)) (1 : k) * q).coeff d ≠ 0) :
    ∀ i, e i * b i ≤ d i := by
  let s : σ →₀ Nat := Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i)
  have hs : s ≤ d := by
    by_contra hn
    have hz : (MvPolynomial.monomial s (1 : k) * q).coeff d = 0 := by
      rw [MvPolynomial.coeff_monomial_mul']
      simp [hn]
    exact h hz
  intro i
  simpa [s] using hs i
