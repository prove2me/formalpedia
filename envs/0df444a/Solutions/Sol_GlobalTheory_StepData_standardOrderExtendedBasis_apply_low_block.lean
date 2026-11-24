-- Prove2me | solution 1 for GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:24.1868+00:00
-- url     : https://prove2.me/submissions/bb3fee06-e9f6-43ba-b350-c67684cedf52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.StepData
theorem _root_.solution (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : Fin c) :
    stdOrd κ t j c h (.inl (.inr ⟨i.val, by omega⟩)) = .inr i := by
  have : finCongr (by omega : l = c + j) ⟨i.val, by omega⟩ = Fin.castAdd j i := rfl
  simp [stdOrd, this]
end GlobalTheory.StepData
