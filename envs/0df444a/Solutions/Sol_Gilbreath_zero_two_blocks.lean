-- Prove2me | solution 1 for Gilbreath.zero_two_blocks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-24T23:06:43.096102+00:00
-- url     : https://prove2.me/submissions/d5a35c5d-925b-42b2-8182-824c98833ea5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Gilbreath_chase_hunter_tao_finite_criterion
import Theorems.Thm_Gilbreath_prime_gap_finite_criterion_conditions

namespace Gilbreath

private theorem absDiff_two_mul (a : ℕ → ℕ) (n : ℕ) :
    absDiff (fun j => 2 * a j) n = 2 * absDiff a n := by
  simp only [absDiff, Nat.cast_mul, Nat.cast_ofNat]
  have h : (2 : ℤ) * (a (n + 1) : ℤ) - 2 * (a n : ℤ) =
      2 * ((a (n + 1) : ℤ) - (a n : ℤ)) := by ring
  rw [h, Int.natAbs_mul]
  norm_num

theorem iterAbsDiff_two_mul (a : ℕ → ℕ) (k n : ℕ) :
    iterAbsDiff (fun j => 2 * a j) k n = 2 * iterAbsDiff a k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      change absDiff (iterAbsDiff (fun j => 2 * a j) k) n =
        2 * absDiff (iterAbsDiff a k) n
      have hf : iterAbsDiff (fun j => 2 * a j) k =
          fun j => 2 * iterAbsDiff a k j := by
        funext j
        exact ih j
      rw [hf]
      exact absDiff_two_mul (iterAbsDiff a k) n

theorem iterAbsDiff_shift (a : ℕ → ℕ) (k n : ℕ) :
    iterAbsDiff (fun j => a (j + 1)) k n = iterAbsDiff a k (n + 1) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      change absDiff (iterAbsDiff (fun j => a (j + 1)) k) n =
        absDiff (iterAbsDiff a k) (n + 1)
      simp [absDiff, ih, Nat.add_assoc]

theorem half_tail_exists
    (h_even : ∀ n, Even (d 1 (n + 1))) :
    ∃ b : ℕ → ℕ, ∀ n, d 1 (n + 1) = 2 * b n := by
  choose b hb using h_even
  refine ⟨b, ?_⟩
  intro n
  simpa [two_mul] using hb n

theorem d_normalized_tail (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (k n : ℕ) :
    d (k + 1) (n + 1) = 2 * iterAbsDiff b k n := by
  have hd : d (k + 1) = iterAbsDiff (d 1) k := by
    simpa [Nat.add_comm] using (iterAbsDiff_d 1 k).symm
  rw [hd]
  rw [← iterAbsDiff_shift (d 1) k n]
  have hfun : (fun j => d 1 (j + 1)) = fun j => 2 * b j := by
    funext j
    exact hb j
  rw [hfun, iterAbsDiff_two_mul]

theorem zero_two_blocks_of_normalized_tail (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n)
    (hgood : ∀ k, iterAbsDiff b k 0 = 0 ∨ iterAbsDiff b k 0 = 1)
    (K : ℕ) :
    ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧
      ∀ n, 1 ≤ n → n ≤ m + 1 → d k n = 0 ∨ d k n = 2 := by
  refine ⟨K + 1, 0, by omega, by omega, ?_⟩
  intro n hn hnm
  have hn1 : n = 1 := by omega
  subst n
  have hd := d_normalized_tail b hb K 0
  rcases hgood K with hz | ho
  · left
    simpa [hz] using hd
  · right
    simpa [ho] using hd

end Gilbreath

open Gilbreath

theorem solution (K : ℕ) :
    ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧
      ∀ n, 1 ≤ n → n ≤ m + 1 → d k n = 0 ∨ d k n = 2 := by
  obtain ⟨b, hb, N₀, hsmall, hlarge⟩ :=
    Gilbreath.prime_gap_finite_criterion_conditions
  apply Gilbreath.zero_two_blocks_of_normalized_tail b hb
  intro k
  by_cases hk : k + 1 ≤ N₀
  · simpa using hsmall (k + 1) (by omega) hk
  · obtain ⟨N', M, L, R, hbounds, hinput, hzero, htwo⟩ :=
      hlarge (k + 1) (by omega)
    simpa using Gilbreath.chase_hunter_tao_finite_criterion
      b (k + 1) N' M L R hbounds hinput hzero htwo
