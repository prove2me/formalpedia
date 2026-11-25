-- Prove2me | solution 1 for GlobalTheory.T.simpleOverStableSubmodule_piTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:34.619351+00:00
-- url     : https://prove2.me/submissions/b9cd360b-6b01-400b-997b-0de9ecf0374f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensorStatement
import Theorems.Thm_GlobalTheory_PiSimple_simpleOver_piKer


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
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.PiSimple.simpleOver_piKer | exact GlobalTheory.PiSimple.simpleOver_piKer | (intros; apply GlobalTheory.PiSimple.simpleOver_piKer <;> assumption)
end _root_.GlobalTheory.T
