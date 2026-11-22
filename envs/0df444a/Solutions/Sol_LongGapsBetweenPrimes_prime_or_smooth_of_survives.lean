-- Prove2me | solution 1 for LongGapsBetweenPrimes.prime_or_smooth_of_survives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:06.502809+00:00
-- url     : https://prove2.me/submissions/8bc9d3c2-1806-457d-8636-edb804533759

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {n H : ℕ} {x w z : ℝ}
    (hn : 1 ≤ n) (hnH : n ≤ H) (hx : 0 < x) (hsmall : 2 * (H : ℝ) < x * w)
    (hsurvives : ∀ p : ℕ, p.Prime → ((p : ℝ) ≤ w ∨ (z < p ∧ (p : ℝ) ≤ x / 2)) → ¬p ∣ n) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z := by
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  right
  intro p hp hpn
  by_contra! hpz
  have hpbig : x / 2 < (p : ℝ) := by
    by_contra! hpx
    exact hsurvives p hp (Or.inr ⟨hpz, hpx⟩) hpn
  obtain ⟨k, rfl⟩ := hpn
  have hk1 : k ≠ 1 := by
    intro hk
    simp [hk, hp] at hprime
  obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
  have hqn : q ∣ p * k := dvd_mul_of_dvd_right hqk p
  have hqbig : w < (q : ℝ) := by
    by_contra! hqw
    exact hsurvives q hq (Or.inl hqw) hqn
  have hkn : q ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero (by rintro rfl; simp at hn)) hqk
  have hpkH : (p : ℝ) * k ≤ H := by exact_mod_cast hnH
  have hqk' : (q : ℝ) ≤ k := by exact_mod_cast hkn
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  nlinarith [mul_le_mul_of_nonneg_left hqk' hp0,
    mul_lt_mul_of_pos_right hpbig hq0,
    mul_lt_mul_of_pos_left hqbig hx]
end LongGapsBetweenPrimes
