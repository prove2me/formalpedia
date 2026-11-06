-- Prove2me | solution 1 for OAI.SevenEighths.HeathBrownIteration.step_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:45.723223+00:00
-- url     : https://prove2.me/submissions/c1bcc49b-c7a5-4947-bdea-db6706343cc6

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_HeathBrownIteration
import Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_step_sub

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.HeathBrownIteration
noncomputable section
namespace OAI.SevenEighths.HeathBrownIteration
theorem _root_.solution {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith
end OAI.SevenEighths.HeathBrownIteration
