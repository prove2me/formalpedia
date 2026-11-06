-- Prove2me | solution 1 for OAI.SevenEighths.HeathBrownIteration.step_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:15.484773+00:00
-- url     : https://prove2.me/submissions/e5dfc63d-4521-4560-b7a3-4d5e617bdb81

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
namespace OAI.SevenEighths.HeathBrownIteration
theorem _root_.solution (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring
end OAI.SevenEighths.HeathBrownIteration
