-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.exact_kerMap_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:03.192001+00:00
-- url     : https://prove2.me/submissions/d2c66e5d-8b04-4c2b-ac97-5bcd1d05d706

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
theorem _root_.solution (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (kerMap g b) (delta f g hf hg hfg b) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.ker (LinearMap.lsmul A M₂ b)).subtype (LinearMap.exact_subtype_ker_map _)
    _ _ _ _ _ _ (kerMap g b) (by ext x; rfl) Subtype.val_injective
end GlobalTheory.ScalarSnakeLength
