-- Prove2me | solution 1 for GlobalTheory.PiSimple.pp_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:27:42.666536+00:00
-- url     : https://prove2.me/submissions/6325ff47-193f-4494-a0e8-f3c1c543e13a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_pp_empty
import Theorems.Thm_GlobalTheory_PiSimple_pp_of_equiv
import Theorems.Thm_GlobalTheory_PiSimple_pp_option

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
theorem _root_.solution (σ : Type) [Finite σ] : PP σ :=
  Finite.induction_empty_option (P := PP) (fun f h => pp_of_equiv f h) pp_empty
    (fun h => pp_option h) σ
end GlobalTheory.PiSimple
