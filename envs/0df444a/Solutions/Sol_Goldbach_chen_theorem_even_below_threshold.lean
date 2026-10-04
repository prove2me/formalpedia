-- Prove2me | solution 1 for Goldbach.chen_theorem_even_below_threshold
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:07:51.0016+00:00
-- url     : https://prove2.me/submissions/a735e183-6458-4164-8319-4a59d18afde1

import Mathlib

theorem solution : ¬ (∀ (N₀ : ℕ),
    ∀ n : ℕ, Even n → n < N₀ →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧ n = p + q) := by
  intro h
  obtain ⟨p, q, hp, -, hn⟩ := h 1 0 ⟨0, rfl⟩ Nat.one_pos
  have := hp.two_le
  omega
