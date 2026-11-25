-- Prove2me | solution 1 for GlobalTheory.HermForm.unitaryGroup.toEnd_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:50:47.035927+00:00
-- url     : https://prove2.me/submissions/941603b9-9931-47c7-bcb3-f933c0ccb20a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (h : HermForm R M)
variable {h}
open GlobalTheory.HermForm.unitaryGroup
namespace GlobalTheory.HermForm.unitaryGroup
theorem _root_.solution : Function.Injective (toEnd h) :=
  fun _ _ H => ext fun x => congrArg (fun f : Module.End R M => f x) H
end GlobalTheory.HermForm.unitaryGroup
