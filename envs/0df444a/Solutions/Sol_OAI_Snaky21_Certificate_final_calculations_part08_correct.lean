-- Prove2me | solution 1 for OAI.Snaky21.Certificate.final_calculations_part08_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:48:58.545575+00:00
-- url     : https://prove2.me/submissions/25a69504-fea4-4e91-ad4c-587673947e47

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl

theorem calc11_finishA_2427 : calc11_set_2426.erase (8, 8) = card_727.required := by decide +kernel
theorem calc11_finishT_2427 : insert (8, 8) calc11_set_2394 = card_727.envelope := by decide +kernel
end OAI.Snaky21.Certificate

theorem solution : (calc11_set_2426.erase (8, 8) = card_727.required) ∧ (insert (8, 8) calc11_set_2394 = card_727.envelope) ∧ True :=
  ⟨calc11_finishA_2427, calc11_finishT_2427, True.intro⟩
