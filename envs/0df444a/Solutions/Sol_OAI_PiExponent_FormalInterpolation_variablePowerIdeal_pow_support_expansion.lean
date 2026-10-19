-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.variablePowerIdeal_pow_support_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:46:48.125787+00:00
-- url     : https://prove2.me/submissions/add5ce90-2c15-4ad7-8c11-7ac8c13e0a96

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePowerIdeal_pow_mem_expansion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coeff_nonzero_of_finsum

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e : σ → Nat) (n : Nat) (p : MvPolynomial σ k)
    (hp : p ∈ (Ideal.span (Set.range
      (fun i : σ => (MvPolynomial.X i : MvPolynomial σ k) ^ e i))) ^ n)
    (d : σ →₀ Nat) (hd : p.coeff d ≠ 0) :
    ∃ (m : Nat) (b : Fin m → σ → Nat)
      (q : Fin m → MvPolynomial σ k),
      (∀ j, (∑ i, b j i) = n) ∧
      p = ∑ j, MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b j i)) (1 : k) * q j ∧
      ∃ j, (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b j i)) (1 : k) * q j).coeff d ≠ 0 := by
  obtain ⟨m, b, q, hb, hp_eq⟩ :=
    OAI.PiExponent.FormalInterpolation.variablePowerIdeal_pow_mem_expansion e n p hp
  refine ⟨m, b, q, hb, hp_eq, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.coeff_nonzero_of_finsum
    m (fun j => MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b j i)) (1 : k) * q j)
    p d hp_eq hd