-- Prove2me | solution 2 for OAI.SevenEighths.HeathBrownIteration.step_gt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:13.494469+00:00
-- url     : https://prove2.me/submissions/d5d8b776-34df-4990-a948-dc4e6ef87e01

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

theorem solution {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  unfold step
  apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 3 * x - 1)).2
  linarith
