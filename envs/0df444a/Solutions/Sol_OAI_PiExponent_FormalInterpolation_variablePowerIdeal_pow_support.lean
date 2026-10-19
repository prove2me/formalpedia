-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.variablePowerIdeal_pow_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:41:50.820818+00:00
-- url     : https://prove2.me/submissions/526daa79-726c-46f3-9a20-949928aebaaa

import Mathlib.RingTheory.MvPolynomial.Ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePowerIdeal_pow_support_expansion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePowerIdeal_monomial_mul_coeff_support

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e : σ → Nat) (n : Nat) (p : MvPolynomial σ k)
    (hp : p ∈ (Ideal.span (Set.range
      (fun i : σ => (MvPolynomial.X i : MvPolynomial σ k) ^ e i))) ^ n)
    (d : σ →₀ Nat) (hd : p.coeff d ≠ 0) :
    ∃ b : σ → Nat, (∑ i, b i) = n ∧ ∀ i, e i * b i ≤ d i := by
  obtain ⟨m, b, q, hb, hrepr, j, hj⟩ :=
    OAI.PiExponent.FormalInterpolation.variablePowerIdeal_pow_support_expansion
      e n p hp d hd
  refine ⟨b j, hb j, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.variablePowerIdeal_monomial_mul_coeff_support
    e (b j) (q j) d hj