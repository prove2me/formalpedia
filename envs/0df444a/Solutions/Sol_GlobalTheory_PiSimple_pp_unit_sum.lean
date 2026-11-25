-- Prove2me | solution 1 for GlobalTheory.PiSimple.pp_unit_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:41.98045+00:00
-- url     : https://prove2.me/submissions/8402eefc-84ab-45ab-ae2a-24785f13a73a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_pp_unit
import Theorems.Thm_GlobalTheory_PiSimple_simpleOver_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead
namespace GlobalTheory.PiSimple
theorem _root_.solution {α : Type} (hα : PP α) : PP (PUnit ⊕ α) := by
  intro _ N _ _ Op K hr hs hso
  refine simpleOver_sum pp_unit hα N Op K hr ?_ hs hso
  rw [(PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun u : PUnit => N (Sum.inl u))
    PUnit.unit).rank_eq]
  exact hr _
end GlobalTheory.PiSimple
