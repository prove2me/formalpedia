-- Prove2me | solution 1 for Matrix.diagonal_sandwich_apply
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T00:19:00.506591+00:00
-- url     : https://prove2.me/submissions/8c30a9af-291d-4c05-8a96-12af7f605d38

import Mathlib

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D A : Matrix ι ι ℂ)
    (hD : ∀ x y, x ≠ y → D x y = 0) (y z : ι) :
    (D * A * D) y z = D y y * A y z * D z z := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single z]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single y]
    · intro x _ hx
      simp [hD y x hx.symm]
    · simp
  · intro x _ hx
    simp [hD x z hx]
  · simp
