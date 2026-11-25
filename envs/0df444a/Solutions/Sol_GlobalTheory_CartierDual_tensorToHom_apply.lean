-- Prove2me | solution 1 for GlobalTheory.CartierDual.tensorToHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:30:00.391944+00:00
-- url     : https://prove2.me/submissions/bafb5470-68b1-43c7-a0af-ec78582ffc60

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open GlobalTheory.CartierDual
variable {R N M N' M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
namespace GlobalTheory.CartierDual
theorem _root_.solution (x : N ⊗[R] M) (φ : CartierDual R M) :
    tensorToHom R N M x φ = TensorProduct.rid R N (LinearMap.lTensor N φ.ofConv x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul n m => simp
end GlobalTheory.CartierDual
