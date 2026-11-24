-- Prove2me | solution 1 for GlobalTheory.rightContract_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:41.362157+00:00
-- url     : https://prove2.me/submissions/ae2fe7a8-a33b-4b83-bb6b-79da9bbbdc1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport
import Theorems.Thm_GlobalTheory_rightContract_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [rightContract_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory
