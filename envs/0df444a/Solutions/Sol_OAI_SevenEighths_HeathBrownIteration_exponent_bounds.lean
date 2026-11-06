-- Prove2me | solution 1 for OAI.SevenEighths.HeathBrownIteration.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:50.744357+00:00
-- url     : https://prove2.me/submissions/9f5ea82e-5eff-4c44-8b24-3fbf1afe0254

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

theorem solution (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  have step_gt : ∀ {x : ℝ}, (4 / 3 : ℝ) < x → (4 / 3 : ℝ) < step x := by
    intro x hx
    have hden : (0 : ℝ) < 3 * x - 1 := by linarith
    apply (lt_div_iff₀ hden).2
    linarith
  have step_lt : ∀ {x : ℝ}, (4 / 3 : ℝ) < x → step x < x := by
    intro x hx
    have hden : (0 : ℝ) < 3 * x - 1 := by linarith
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos (show (0 : ℝ) < 3 * x - 4 by linarith)
      (show (0 : ℝ) < x - 1 by linarith)]
  induction n with
  | zero => norm_num [exponent]
  | succ n ih => exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩
