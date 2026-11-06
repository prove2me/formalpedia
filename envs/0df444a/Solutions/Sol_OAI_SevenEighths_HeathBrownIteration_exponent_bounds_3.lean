-- Prove2me | solution 3 for OAI.SevenEighths.HeathBrownIteration.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:22.484992+00:00
-- url     : https://prove2.me/submissions/7c492b95-406d-4a12-8183-30c4e6f38d21

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_HeathBrownIteration
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.HeathBrownIteration
noncomputable section
theorem OA1Aux.step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have h : 3 * x - 1 ≠ 0 := by intro h; linarith
  have e : (6 * x - 4) / (3 * x - 1) * (3 * x - 1) = 6 * x - 4 := div_mul_cancel₀ _ h
  rw [eq_div_iff h]
  unfold step
  rw [sub_mul, e]
  ring

theorem solution (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => simp [exponent]; norm_num
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : exponent (n + 1) = step (exponent n) := rfl
    rw [e]
    constructor
    · have := OA1Aux.step_sub (exponent n) h1.le
      have h3 : 0 < 2 * (exponent n - 4 / 3) / (3 * exponent n - 1) :=
        div_pos (by linarith) (by linarith)
      linarith
    · unfold step
      rw [div_le_iff₀ (by linarith)]
      linarith
