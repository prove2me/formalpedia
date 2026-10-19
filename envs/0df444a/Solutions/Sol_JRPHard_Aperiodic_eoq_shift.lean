-- Prove2me | solution 1 for JRPHard.Aperiodic.eoq_shift
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:48:37.972923+00:00
-- url     : https://prove2.me/submissions/aeeb5c4f-3e86-4f44-b28b-a2c4e6049283

import Definitions.Def_JRPHard_Aperiodic_Setting
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open JRPHard.Aperiodic

theorem solution (M : ℕ) (hM : 2 ≤ M) :
    (eoq2 M (M + 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) + 1) ∧
      (coefK0 M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) + 1)) ∧
    (eoq2 M (M - 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) - 1) ∧
      (coefK0 M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) - 1)) := by
  have hM1 : 1 ≤ M := by omega
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hminus : 0 < (M : ℝ) - 1 := by linarith
  have hplus : 0 < (M : ℝ) + 1 := by linarith
  have hH : (coefH2 M : ℝ) = (M : ℝ) * ((M : ℝ) ^ 2 - 1) := by
    simp [coefH2, Nat.cast_sub hM2]
  have hK : (coefK0 M : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    simp [coefK0, Nat.cast_sub hM1]
  have heoq (q : ℕ) : eoq2 M q = (M : ℝ) ^ 3 * ((M : ℝ) ^ 2 - 1) / q +
      (M : ℝ) * ((M : ℝ) ^ 2 - 1) * q := by
    simp [eoq2, eoq, coefK2, coefH2, Nat.cast_sub hM2]
  constructor
  · constructor
    · rw [heoq, heoq, hH]
      push_cast
      field_simp
      <;> ring
    · rw [hK, hH]
      apply (le_div_iff₀ hplus).mpr
      nlinarith
  · constructor
    · rw [heoq, heoq, hH, Nat.cast_sub hM1, Nat.cast_one]
      field_simp
      <;> ring
    · rw [hK, hH]
      apply (le_div_iff₀ hminus).mpr
      nlinarith [mul_nonneg (show 0 ≤ (M : ℝ) by positivity) hminus.le]
