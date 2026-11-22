-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_primeProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:00.131806+00:00
-- url     : https://prove2.me/submissions/e933de5a-671a-4319-aa11-c09d89cd4fd1

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) (γ : ℝ) :
    divisorEulerMoment (∏ p ∈ ps, p) γ =
      ∏ p ∈ ps, (1 + (p : ℝ) ^ γ / ((p : ℝ) - 1)) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun n => (n : ℝ) ^ γ / n.totient, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · simp [f]
    · intro a b hab
      change ((a * b : ℕ) : ℝ) ^ γ / ((a * b).totient : ℝ) =
        ((a : ℝ) ^ γ / a.totient) * ((b : ℝ) ^ γ / b.totient)
      rw [Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact (div_mul_div_comm _ _ _ _).symm
  have hsq : Squarefree (∏ p ∈ ps, p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hps p hp) (hps q hq)).mpr hpq))
      (fun p hp => (hps p hp).squarefree)
  have h := hf.prodPrimeFactors_one_add_of_squarefree hsq
  rw [Nat.primeFactors_prod hps] at h
  calc
    _ = ∏ p ∈ ps, (1 + f p) := h.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      change 1 + (p : ℝ) ^ γ / p.totient = _
      rw [Nat.totient_prime (hps p hp), Nat.cast_sub (hps p hp).one_le, Nat.cast_one]
end LongGapsBetweenPrimes
