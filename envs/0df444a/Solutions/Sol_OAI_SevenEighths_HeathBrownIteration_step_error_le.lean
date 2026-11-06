-- Prove2me | solution 1 for OAI.SevenEighths.HeathBrownIteration.step_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:46.964689+00:00
-- url     : https://prove2.me/submissions/9bc0f534-503a-4e72-99fd-1d6b51848202

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
theorem _root_.solution {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]
end OAI.SevenEighths.HeathBrownIteration
