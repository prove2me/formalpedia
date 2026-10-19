-- Prove2me | solution 1 for OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:38:39.879603+00:00
-- url     : https://prove2.me/submissions/6947847b-608d-4340-80b2-133cfda97919

import Mathlib

theorem solution {n m : ℕ}
    (hm : 0 < m) (hnm : n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨s, u, hu, hmu⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) hm.ne'
  refine ⟨s, u, ?_, hu.pos, hu, ?_⟩
  · rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      subst h hnm
      simp at hmu
      subst hmu
      exact (Nat.not_even_iff_odd.2 (hu.pow)) heven
    · exact h
  · subst hnm hmu; ring
