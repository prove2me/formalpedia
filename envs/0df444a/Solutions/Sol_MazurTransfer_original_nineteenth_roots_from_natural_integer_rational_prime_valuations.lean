-- Prove2me | solution 1 for MazurTransfer.original_nineteenth_roots_from_natural_integer_rational_prime_valuations
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T20:10:49.827984+00:00
-- url     : https://prove2.me/submissions/48cec04f-d60d-4d5b-9a4c-fbb82bec6d2d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original constructive nineteenth-root criteria for natural numbers, integers, nonzero rationals and rational units from their prime valuation divisibility, retaining each original nonzero and sign hypothesis.
Named downstream consumer: zero detection by rational power-class valuation coordinates and the original pi Selmer dimension bound.
-/
import Mathlib
noncomputable section
open scoped BigOperators
namespace MazurTransfer.NineteenthRootsFromPrimeValuationsProofBoundary20261019
end MazurTransfer.NineteenthRootsFromPrimeValuationsProofBoundary20261019
namespace MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019
theorem nat_exists_nineteenth_root (n : ℕ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n) :
    ∃ r : ℕ, r ^ 19 = n := by
  let r := n.factorization.prod (fun p k => p ^ (k / 19))
  refine ⟨r, ?_⟩
  calc
    r ^ 19 = n.factorization.prod (fun p k => p ^ k) := by
      change (∏ p ∈ n.factorization.support, p ^ (n.factorization p / 19)) ^ 19 =
        ∏ p ∈ n.factorization.support, p ^ n.factorization p
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, Nat.div_mul_cancel]
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
      exact hval p (Nat.prime_of_mem_primeFactors hp)
    _ = n := Nat.prod_factorization_pow_eq_self hn
theorem rat_num_den_valuation_divisibility (a : ℚ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a)
    (p : ℕ) (hp : p.Prime) :
    19 ∣ padicValNat p a.num.natAbs ∧ 19 ∣ padicValNat p a.den := by
  by_cases hd : p ∣ a.den
  · have hn : ¬ p ∣ a.num.natAbs := by
      intro hn
      have h := Nat.dvd_gcd hn hd
      rw [a.reduced.gcd_eq_one] at h
      exact hp.ne_one (Nat.dvd_one.mp h)
    have h := hval p hp
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hn] at h
    have h' : (19 : ℤ) ∣ -(padicValNat p a.den : ℤ) := by simpa using h
    refine ⟨?_, ?_⟩
    · rw [padicValNat.eq_zero_of_not_dvd hn]
      exact dvd_zero _
    · exact_mod_cast (Int.dvd_neg.mp h')
  · have h := hval p hp
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hd] at h
    have h' : (19 : ℤ) ∣ (padicValNat p a.num.natAbs : ℤ) := by simpa using h
    refine ⟨?_, ?_⟩
    · exact_mod_cast h'
    · rw [padicValNat.eq_zero_of_not_dvd hd]
      exact dvd_zero _
theorem int_exists_nineteenth_root (n : ℤ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n.natAbs) :
    ∃ r : ℤ, r ^ 19 = n := by
  obtain ⟨r, hr⟩ := nat_exists_nineteenth_root n.natAbs (Int.natAbs_ne_zero.mpr hn) hval
  have hcast : (r : ℤ) ^ 19 = (n.natAbs : ℤ) := by exact_mod_cast hr
  by_cases h : 0 ≤ n
  · refine ⟨r, ?_⟩
    rw [hcast, Int.natCast_natAbs, abs_of_nonneg h]
  · refine ⟨-(r : ℤ), ?_⟩
    rw [show (-(r : ℤ)) ^ 19 = -((r : ℤ) ^ 19) by ring, hcast,
      Int.natCast_natAbs, abs_of_neg (lt_of_not_ge h), neg_neg]
theorem rat_exists_nineteenth_root (a : ℚ) (ha : a ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a) :
    ∃ b : ℚ, b ^ 19 = a := by
  obtain ⟨n, hn⟩ := int_exists_nineteenth_root a.num (Rat.num_ne_zero.mpr ha)
    (fun p hp => (rat_num_den_valuation_divisibility a hval p hp).1)
  obtain ⟨d, hd⟩ := nat_exists_nineteenth_root a.den a.den_nz
    (fun p hp => (rat_num_den_valuation_divisibility a hval p hp).2)
  refine ⟨(n : ℚ) / (d : ℚ), ?_⟩
  rw [div_pow, ← Int.cast_pow, hn, ← Nat.cast_pow, hd]
  exact Rat.num_div_den a
theorem unit_exists_nineteenth_root (a : ℚˣ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p (a : ℚ)) :
    ∃ b : ℚˣ, b ^ 19 = a := by
  obtain ⟨b, hb⟩ := rat_exists_nineteenth_root (a : ℚ) (Units.ne_zero a) hval
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hb
    exact (Units.ne_zero a) hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext hb⟩
end MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019
theorem solution : (∀ (n : ℕ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n), ∃ r : ℕ, r ^ 19 = n) ∧ (∀ (a : ℚ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a)
    (p : ℕ) (hp : p.Prime), 19 ∣ padicValNat p a.num.natAbs ∧ 19 ∣ padicValNat p a.den) ∧ (∀ (n : ℤ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n.natAbs), ∃ r : ℤ, r ^ 19 = n) ∧ (∀ (a : ℚ) (ha : a ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a), ∃ b : ℚ, b ^ 19 = a) ∧ (∀ (a : ℚˣ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p (a : ℚ)), ∃ b : ℚˣ, b ^ 19 = a) := by
  exact ⟨MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019.nat_exists_nineteenth_root, MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019.rat_num_den_valuation_divisibility, MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019.int_exists_nineteenth_root, MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019.rat_exists_nineteenth_root, MazurTransfer.OriginalNineteenthRootsFromPrimeValuationsProof20261019.unit_exists_nineteenth_root⟩
#print axioms solution
