-- Prove2me | solution 2 for OAI.SevenEighths.HeathBrownIteration.step_error_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:35.313596+00:00
-- url     : https://prove2.me/submissions/2a19ed45-6b00-4aa2-8e10-1924fc1ce9e7

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

theorem solution {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [OA1Aux.step_sub x hx, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (x - 4 / 3)]
