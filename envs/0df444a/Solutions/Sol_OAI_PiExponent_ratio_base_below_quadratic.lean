-- Prove2me | solution 1 for OAI.PiExponent.ratio_base_below_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T23:20:15.322964+00:00
-- url     : https://prove2.me/submissions/b24e995f-3647-4a7e-b6ce-01144d9ca9a9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution
    (theta : ℚ) (A : ℝ)
    (htheta : 0 < theta) (hA : 0 < A)
    (hquadratic : A ^ 2 < (theta : ℝ)) :
    ∃ R : ℝ, 1 < R ∧ R ^ 2 < (theta : ℝ) / A ^ 2 := by
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have hq : 1 < (theta : ℝ) / A ^ 2 := (one_lt_div hA2).2 hquadratic
  let q : ℝ := (theta : ℝ) / A ^ 2
  have hq' : 1 < q := by simpa [q] using hq
  have hqpos : 0 < q := by linarith
  let R : ℝ := 1 + (q - 1) / (2 * q)
  have hR : 1 < R := by
    dsimp [R]
    linarith [div_pos (show 0 < q - 1 by linarith)
      (show 0 < 2 * q by exact mul_pos (by norm_num) hqpos)]
  have hgap : 0 < q - R ^ 2 := by
    have heq : q - R ^ 2 = ((q - 1) ^ 2 * (4 * q - 1)) / (4 * q ^ 2) := by
      dsimp [R]
      field_simp [ne_of_gt hqpos]
      <;> ring
    rw [heq]
    apply div_pos
    · exact mul_pos (sq_pos_of_pos (by linarith)) (by nlinarith)
    · exact mul_pos (by norm_num) (sq_pos_of_pos hqpos)
  refine ⟨R, hR, ?_⟩
  dsimp [q] at hgap ⊢
  linarith
