-- Prove2me | solution 2 for OAI.SevenEighths.HeathBrownIteration.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:37.685775+00:00
-- url     : https://prove2.me/submissions/38f470bf-11b2-4902-ad56-258b46caa017

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_HeathBrownIteration
import Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_step_gt
import Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_step_lt

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.HeathBrownIteration
noncomputable section
namespace OAI.SevenEighths.HeathBrownIteration
theorem _root_.solution (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩
end OAI.SevenEighths.HeathBrownIteration
