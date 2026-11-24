-- Prove2me | solution 1 for GlobalTheory.StepData.Level.mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:46.566494+00:00
-- url     : https://prove2.me/submissions/ed9cba43-6fbb-47d9-b8a7-7a574930c05e

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
theorem _root_.solution {G G' : Type*} [Group G] [Group G'] {φ : G ≃* G'} {P : Level G} {h : G'} :
    h ∈ (P.map φ).J ↔ φ.symm h ∈ P.J := Iff.rfl
end Level
end GlobalTheory.StepData
