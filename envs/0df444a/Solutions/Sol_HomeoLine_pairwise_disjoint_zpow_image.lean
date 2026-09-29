-- Prove2me | solution 1 for HomeoLine.pairwise_disjoint_zpow_image
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T09:08:08.661299+00:00
-- url     : https://prove2.me/submissions/e7a2c4c4-0f2c-454b-8964-455575c9b632

import Mathlib

theorem solution {z : ℝ ≃o ℝ} {c d : ℝ} (hcd : c ≤ d) (hz : d < z c) :
    ∀ m n : ℤ, m ≠ n →
      Disjoint (Set.Ioo ((z ^ m) c) ((z ^ m) d)) (Set.Ioo ((z ^ n) c) ((z ^ n) d)) := by
  have hcz : c < z c := lt_of_le_of_lt hcd hz
  -- the forward orbit of `c` is strictly increasing
  have step : ∀ (k : ℕ) (y : ℝ), (z ^ (k + 2 : ℕ)) y = (z ^ (k + 1 : ℕ)) (z y) := by
    intro k y; rw [pow_succ]; rfl
  have up : ∀ n : ℕ, c < (z ^ (n + 1 : ℕ)) c := by
    intro n
    induction n with
    | zero => simpa using hcz
    | succ k ih => rw [step k c]; exact lt_trans ih ((z ^ (k + 1 : ℕ)).strictMono hcz)
  have upz : ∀ j : ℤ, 0 < j → c < (z ^ j) c := by
    intro j hj
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j = ((k + 1 : ℕ) : ℤ) := ⟨(j - 1).toNat, by omega⟩
    rw [hk, zpow_natCast]
    exact up k
  -- hence strictly increasing in the exponent
  have mono : ∀ m n : ℤ, m < n → (z ^ m) c < (z ^ n) c := by
    intro m n hmn
    have h1 : (z ^ n) c = (z ^ m) ((z ^ (n - m)) c) := by
      show _ = ((z ^ m) * (z ^ (n - m))) c
      rw [← zpow_add]; congr 2; ring
    rw [h1]
    exact (z ^ m).strictMono (upz (n - m) (by omega))
  -- each interval ends strictly before the next begins
  have dstep : ∀ k : ℤ, (z ^ k) d < (z ^ (k + 1)) c := by
    intro k
    have h1 : (z ^ (k + 1)) c = (z ^ k) (z c) := by rw [zpow_add, zpow_one]; rfl
    rw [h1]
    exact (z ^ k).strictMono hz
  have gap : ∀ m n : ℤ, m < n → (z ^ m) d < (z ^ n) c := by
    intro m n h
    rcases eq_or_lt_of_le (Int.add_one_le_iff.mpr h) with he | hl
    · rw [← he]; exact dstep m
    · exact lt_trans (dstep m) (mono (m + 1) n hl)
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [Set.disjoint_left]
    intro x hx hx2
    linarith [hx.2, hx2.1, gap m n h]
  · rw [Set.disjoint_left]
    intro x hx hx2
    linarith [hx.1, hx2.2, gap n m h]
