-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.asymptotic_representatives_of_eventual_weighted_surjectivity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:04:06.230341+00:00
-- url     : https://prove2.me/submissions/a92b752e-7649-46b5-ab7d-5dec67da1c02

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat)
    (rho : Rat) (hrho : 0 ≤ rho) (eps : Real) (heps : 0 < eps)
    (heventual : ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps)) :
    ∃ C : Nat, ∀ n : Nat, ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) + (C : Real) := by
  classical
  obtain ⟨N, hN⟩ := heventual
  set C : Nat := Nat.ceil ((N : Real) * ((rho : Real) + eps))
  refine ⟨C, ?_⟩
  intro n p
  by_cases hn : N ≤ n
  · obtain ⟨q, hqmem, hqwt⟩ := hN n hn p
    refine ⟨q, hqmem, fun a ha => ?_⟩
    exact (hqwt a ha).trans (le_add_of_nonneg_right (Nat.cast_nonneg C))
  · have hn' : n < N := lt_of_not_ge hn
    obtain ⟨q, hqmem, hqwt⟩ := hN N le_rfl p
    refine ⟨q, Ideal.pow_le_pow_right (Nat.le_of_lt hn') hqmem, fun a ha => ?_⟩
    have hbound := hqwt a ha
    have hceil : (N : Real) * ((rho : Real) + eps) ≤ (C : Real) := Nat.le_ceil _
    have hnonneg : (0 : Real) ≤ (n : Real) * ((rho : Real) + eps) := by
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Rat.cast_nonneg.mpr hrho) heps.le)
    nlinarith
