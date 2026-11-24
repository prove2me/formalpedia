-- Prove2me | solution 1 for GlobalTheory.StepData.Level.map_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:39.919987+00:00
-- url     : https://prove2.me/submissions/a463f549-6c68-48cf-adc8-b6f2441b9926

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
namespace Level
theorem _root_.solution {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (P : Level G) (h : (P.map φ).J) :
    (P.map φ).lam h = P.lam ⟨φ.symm h, h.2⟩ := rfl
end Level
end GlobalTheory.StepData
