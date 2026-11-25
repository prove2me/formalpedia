-- Prove2me | solution 1 for GlobalTheory.HermForm.toSesq_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:37.912936+00:00
-- url     : https://prove2.me/submissions/c426b991-08fa-41f4-a364-c0e6cdfda3eb

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
namespace GlobalTheory.HermForm
theorem _root_.solution : Function.Injective (toSesq : HermForm R M → SesqForm R M) :=
  fun _ _ H => ext fun x y => congrArg (fun B : SesqForm R M => B x y) H
end GlobalTheory.HermForm
