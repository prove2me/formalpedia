-- Prove2me | solution 1 for GlobalTheory.StepData.stdOrd_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:10.042287+00:00
-- url     : https://prove2.me/submissions/9b5b57dc-5c5f-4c6c-8b44-6894eb3b2f2e

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
theorem _root_.solution (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (i : κ) :
    stdOrd κ t j c h (.inl (.inl i)) = .inl (.inl (.inl i)) := rfl
end GlobalTheory.StepData
