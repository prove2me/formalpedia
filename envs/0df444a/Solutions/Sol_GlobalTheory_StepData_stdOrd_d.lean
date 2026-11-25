-- Prove2me | solution 1 for GlobalTheory.StepData.stdOrd_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:13.8737+00:00
-- url     : https://prove2.me/submissions/12eea208-b353-41db-a485-81c47a828a7b

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
theorem _root_.solution (κ t : Type*) {l : ℕ} (j c : ℕ) (h : j + c = l) (p : Fin j × t) :
    stdOrd κ t j c h (.inr p) = .inl (.inr p) := rfl
end GlobalTheory.StepData
