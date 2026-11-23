-- Prove2me | solution 1 for KStar.Tree.one_add_pow_prime_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:07:06.845653+00:00
-- url     : https://prove2.me/submissions/6fd6fc77-b796-4738-847d-76e7680f3dec

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_OneAddPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree

theorem KStar.Tree.one_add_pow_prime_pow_eq_one {T : Type} [CommRing T] {l ν M : ℕ} (hl : l.Prime) (h0 : (l : T) ^ (ν + 1) = 0)
    (hM : ν + 1 ≤ M) {x : T} (hx : x ^ l ^ (M - ν - 1) = 0) : (1 + x) ^ l ^ M = 1 := by
  have hA : (l : T) ∣ (1 + x) ^ l ^ (M - ν - 1) - 1 := by
    have hpos : 0 < l ^ (M - ν - 1) := pow_pos hl.pos _
    generalize hN : l ^ (M - ν - 1) = N at hx hpos ⊢
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [add_comm, add_pow]
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hx]
    simp only [zero_mul, add_zero, pow_zero, one_pow, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [add_sub_cancel_right]
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hd : l ∣ Nat.choose (n + 1) (k + 1) := by
      rw [← hN]
      exact hl.dvd_choose_pow (by omega) (by omega)
    obtain ⟨q, hq⟩ := hd
    exact ⟨x ^ (k + 1) * (q : T), by rw [hq]; push_cast; ring⟩
  have hB := dvd_sub_pow_of_dvd_sub (p := l) hA ν
  rw [h0, one_pow, ← pow_mul, ← pow_add] at hB
  have hE : l ^ M = l ^ (M - ν - 1 + ν) * l ^ (M - (M - ν - 1 + ν)) := by
    rw [← pow_add]; congr 1; omega
  rw [zero_dvd_iff, sub_eq_zero] at hB
  rw [hE, pow_mul, hB, one_pow]

theorem solution {T : Type} [CommRing T] {l ν M : ℕ} (hl : l.Prime) (h0 : (l : T) ^ (ν + 1) = 0)
    (hM : ν + 1 ≤ M) {x : T} (hx : x ^ l ^ (M - ν - 1) = 0) : (1 + x) ^ l ^ M = 1 := by
  have hA : (l : T) ∣ (1 + x) ^ l ^ (M - ν - 1) - 1 := by
    have hpos : 0 < l ^ (M - ν - 1) := pow_pos hl.pos _
    generalize hN : l ^ (M - ν - 1) = N at hx hpos ⊢
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [add_comm, add_pow]
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hx]
    simp only [zero_mul, add_zero, pow_zero, one_pow, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [add_sub_cancel_right]
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hd : l ∣ Nat.choose (n + 1) (k + 1) := by
      rw [← hN]
      exact hl.dvd_choose_pow (by omega) (by omega)
    obtain ⟨q, hq⟩ := hd
    exact ⟨x ^ (k + 1) * (q : T), by rw [hq]; push_cast; ring⟩
  have hB := dvd_sub_pow_of_dvd_sub (p := l) hA ν
  rw [h0, one_pow, ← pow_mul, ← pow_add] at hB
  have hE : l ^ M = l ^ (M - ν - 1 + ν) * l ^ (M - (M - ν - 1 + ν)) := by
    rw [← pow_add]; congr 1; omega
  rw [zero_dvd_iff, sub_eq_zero] at hB
  rw [hE, pow_mul, hB, one_pow]
