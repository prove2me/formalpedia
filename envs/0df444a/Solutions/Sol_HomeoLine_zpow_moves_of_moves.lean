-- Prove2me | solution 1 for HomeoLine.zpow_moves_of_moves
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:41:54.360393+00:00
-- url     : https://prove2.me/submissions/098e1ed1-f936-41bd-b73f-e55e1e4e89f4

import Mathlib

theorem solution {f : ℝ ≃o ℝ} {x : ℝ} (hx : f x ≠ x) :
    ∀ m : ℤ, m ≠ 0 → (f ^ m) x ≠ x := by
  have step : ∀ (k : ℕ) (y : ℝ), (f ^ (k + 2 : ℕ)) y = (f ^ (k + 1 : ℕ)) (f y) := by
    intro k y; rw [pow_succ]; rfl
  have up : ∀ n : ℕ, x < f x → x < (f ^ (n + 1 : ℕ)) x := by
    intro n h
    induction n with
    | zero => simpa using h
    | succ k ih => rw [step k x]; exact lt_trans ih ((f ^ (k + 1 : ℕ)).strictMono h)
  have down : ∀ n : ℕ, f x < x → (f ^ (n + 1 : ℕ)) x < x := by
    intro n h
    induction n with
    | zero => simpa using h
    | succ k ih => rw [step k x]; exact lt_trans ((f ^ (k + 1 : ℕ)).strictMono h) ih
  have nat_ne : ∀ n : ℕ, n ≠ 0 → (f ^ n) x ≠ x := by
    intro n hn
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    subst hk
    rcases lt_trichotomy (f x) x with h | h | h
    · exact ne_of_lt (down k h)
    · exact absurd h hx
    · exact ne_of_gt (up k h)
  have int_nat : ∀ k : ℕ, k ≠ 0 → (f ^ (k : ℤ)) x ≠ x := by
    intro k hk; rw [zpow_natCast]; exact nat_ne k hk
  intro m hm hcon
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · have h1 : (f ^ (-m)) ((f ^ m) x) = x := by
      show (f ^ (-m) * f ^ m) x = x
      rw [← zpow_add]; simp
    rw [hcon] at h1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -m = (k : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [hk] at h1
    exact int_nat k (by omega) h1
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, by omega⟩
    rw [hk] at hcon
    exact int_nat k (by omega) hcon
