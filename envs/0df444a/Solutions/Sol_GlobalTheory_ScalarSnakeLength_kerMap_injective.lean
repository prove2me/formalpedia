-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.kerMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:51.55646+00:00
-- url     : https://prove2.me/submissions/28ba2219-4bdf-4fcc-9e9e-cf275c638bd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ScalarSnakeLength
variable {A : Type} [CommRing A]
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]
namespace GlobalTheory.ScalarSnakeLength
theorem _root_.solution (f : M₁ →ₗ[A] M₂) (hf : Function.Injective f) (b : A) :
    Function.Injective (kerMap f b) := fun x y hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))
end GlobalTheory.ScalarSnakeLength
