-- Prove2me | solution 1 for GlobalTheory.T.operatorStable_piTensorPureKernelSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:15.355473+00:00
-- url     : https://prove2.me/submissions/074af8b5-8567-43e1-8b2a-fdf951644701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Theorems.Thm_GlobalTheory_TensHead_stab_piOps_piKer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.TensHead.stab_piOps_piKer | exact GlobalTheory.TensHead.stab_piOps_piKer | (intros; apply GlobalTheory.TensHead.stab_piOps_piKer <;> assumption)
end _root_.GlobalTheory.T
