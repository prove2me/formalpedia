-- Prove2me | solution 8 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:35.03701+00:00
-- url     : https://prove2.me/submissions/b17b3849-9576-48fe-8bdf-705f67ae5166
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hhalf := mathlib_riemannHypothesis s hz htriv hs_one
  linarith
