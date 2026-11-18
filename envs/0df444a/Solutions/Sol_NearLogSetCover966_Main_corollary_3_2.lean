-- Prove2me | solution 1 for NearLogSetCover966.Main.corollary_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:54:09.832985+00:00
-- url     : https://prove2.me/submissions/65afcfd8-f732-4447-a7d9-59c737cce698

import Theorems.Thm_NearLogSetCover966_Main_lemma_3_1
set_option autoImplicit false
open NearLogSetCover966.Main

theorem solution (n : ℕ) (h : ℝ) (hh : 0 ≤ h) (Φ : Bits n → Bool)
    (hΦ : Monotone Φ) :
    (∀ x : Bits n, Φ x ≤ localAcceptance {z | (weight z : ℝ) ≤ h} Φ x) ∧
      ∀ x : Bits n, (weight x : ℝ) ≤ h →
        Φ x = localAcceptance {z | (weight z : ℝ) ≤ h} Φ x := by
  exact lemma_3_1 n {z | (weight z : ℝ) ≤ h} Φ hΦ
