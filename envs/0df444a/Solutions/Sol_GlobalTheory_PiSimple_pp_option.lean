-- Prove2me | solution 1 for GlobalTheory.PiSimple.pp_option
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:32.759709+00:00
-- url     : https://prove2.me/submissions/d703ac58-1b79-4fab-9337-8fb715c8da74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_pp_of_equiv
import Theorems.Thm_GlobalTheory_PiSimple_pp_unit_sum

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
theorem _root_.solution {α : Type} (hα : PP α) : PP (Option α) :=
  pp_of_equiv ((Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _)).symm (pp_unit_sum hα)
end GlobalTheory.PiSimple
