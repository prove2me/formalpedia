-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.total_step_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:35.246216+00:00
-- url     : https://prove2.me/submissions/69cc538a-d53c-4971-a805-24689913918b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by
  nlinarith
end OAI.SevenEighths.InverseMoment
