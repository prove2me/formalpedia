-- Prove2me | solution 1 for Goldbach.chen_representation_six
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:56:27.584267+00:00
-- url     : https://prove2.me/submissions/ff0ac92e-42b7-4a9e-833b-cf1c41808aad

import Mathlib

theorem solution :
    ∃ p q : ℕ, Nat.Prime p ∧
      (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧ 6 = p + q := by
  refine ⟨3, 3, Nat.prime_three, Or.inl Nat.prime_three, rfl⟩
