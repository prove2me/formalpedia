-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.exact_delta_quotMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:01.389138+00:00
-- url     : https://prove2.me/submissions/3da1eef1-a569-477a-b3a1-ce610d6b1b23

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
    Function.Exact (delta f g hf hg hfg b) (quotMap f b) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    _ _ (quotMap f b) (by ext x; rfl) (Submodule.mkQ_surjective _)
end GlobalTheory.ScalarSnakeLength
