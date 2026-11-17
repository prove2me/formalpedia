-- Prove2me | solution 1 for KnodelPrimeCordial.coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:38:17.391195+00:00
-- url     : https://prove2.me/submissions/699f7464-fb3c-4103-ae3e-7ba097513560

import Mathlib

theorem solution {a b : ℕ} (ha : a = 1 ∨ a = 5 ∨ a = 7) (hb₁ : 1 ≤ b)
    (hb₈ : b ≤ 8) (hne : a ≠ b) : Nat.gcd a b = 1 := by
  rcases ha with rfl | rfl | rfl
  all_goals interval_cases b <;> norm_num [Nat.gcd] at *
