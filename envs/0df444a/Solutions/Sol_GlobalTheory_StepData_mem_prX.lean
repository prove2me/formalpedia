-- Prove2me | solution 1 for GlobalTheory.StepData.mem_prX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:32.238968+00:00
-- url     : https://prove2.me/submissions/c7f0e019-dcbf-4047-bb2f-57e6706aece8

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
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.StepData
theorem _root_.solution {C : Subgroup (GL (n ⊕ Fin c) k)} {g : GL n k} :
    g ∈ prX C ↔ ∃ u ∈ N k n c 1, u * embX c g ∈ C := Iff.rfl
end GlobalTheory.StepData
