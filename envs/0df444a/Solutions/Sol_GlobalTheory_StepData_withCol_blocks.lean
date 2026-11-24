-- Prove2me | solution 1 for GlobalTheory.StepData.withCol_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:55:57.324392+00:00
-- url     : https://prove2.me/submissions/b7270b19-a8fa-473b-8d9d-6798b39ac946

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
variable {k : Type*} [Field k] {n n' : Type*}
namespace GlobalTheory.StepData
theorem _root_.solution (x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k) :
    withCol x.toBlocks₁₁ (fun r => x (.inl r) (.inr 0)) = x := by
  ext (r | r) (s | s)
  · rfl
  · rw [Subsingleton.elim (α := Fin 1) s 0]; rfl
  · exact r.elim0
  · exact r.elim0
end GlobalTheory.StepData
