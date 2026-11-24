-- Prove2me | solution 1 for GlobalTheory.GenericLevel.genChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:22.637065+00:00
-- url     : https://prove2.me/submissions/cfcce2f6-f19c-4523-a4a9-b4bd556e517a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.GenericLevel
variable {F a : Type} [Field F] [Fintype a] [DecidableEq a]
namespace GlobalTheory.GenericLevel
theorem _root_.solution (φ : AddChar F Circle) (pos : a → ℕ) (g : upperUnip F pos) :
    ((genChar φ pos g : ℂˣ) : ℂ) = φ (superSum pos ((g : GL a F) : Matrix a a F)) := rfl
end GlobalTheory.GenericLevel
