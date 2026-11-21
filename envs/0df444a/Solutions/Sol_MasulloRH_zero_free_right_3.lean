-- Prove2me | solution 3 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:12:28.774161+00:00
-- url     : https://prove2.me/submissions/01c61a44-a2ad-4653-8c77-fe1d7fdd0c91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_moebius_summatory_rpow_bound
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hM := moebius_summatory_rpow_bound ((s.re - 1 / 2) / 2) (by linarith)
  have hr : (0 : ℝ) ≤ 1 / 2 + (s.re - 1 / 2) / 2 := by linarith
  have hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.re hn
    simp at h
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hstrip :=
    nontrivial_zero_strip_of_moebius_summatory_power_bound hr hM hz hnt hs_one
  linarith
