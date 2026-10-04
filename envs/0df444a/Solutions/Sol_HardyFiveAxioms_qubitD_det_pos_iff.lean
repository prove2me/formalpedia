-- Prove2me | solution 1 for HardyFiveAxioms.qubitD_det_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:07:17.938985+00:00
-- url     : https://prove2.me/submissions/dfb213e5-e630-4bc7-b039-48b95e2b4665

import Mathlib
import Definitions.Def_hardy2001_qubit

open HardyFiveAxioms in
theorem qubitD_det_eq_69c1c573 (a b c : ℝ) :
    (qubitD a b c).det = 4 * (a * b * (1 - a) * (1 - b)) - (c - (1 - a - b + 2 * a * b)) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
  simp [qubitD, Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  norm_num
  ring

open HardyFiveAxioms in
theorem solution (a b c : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    0 < (qubitD a b c).det ↔ cMinus a b < c ∧ c < cPlus a b := by
  have hx : 0 ≤ a * b * (1 - a) * (1 - b) := by
    have h1 : 0 ≤ 1 - a := by linarith
    have h2 : 0 ≤ 1 - b := by linarith
    positivity
  set s := Real.sqrt (a * b * (1 - a) * (1 - b)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a * b * (1 - a) * (1 - b) := Real.sq_sqrt hx
  rw [qubitD_det_eq_69c1c573, cMinus, cPlus, ← hs, ← hs2]
  set m := 1 - a - b + 2 * a * b with hm
  have key : 4 * s ^ 2 - (c - m) ^ 2 = (2 * s - (c - m)) * (2 * s + (c - m)) := by ring
  rw [key]
  constructor
  · intro h
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> linarith
    · exfalso; linarith
  · rintro ⟨h1, h2⟩
    apply mul_pos <;> linarith
