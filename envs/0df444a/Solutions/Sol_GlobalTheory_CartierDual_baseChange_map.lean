-- Prove2me | solution 1 for GlobalTheory.CartierDual.baseChange_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:43.576308+00:00
-- url     : https://prove2.me/submissions/2b2535e1-52e4-4b59-ba77-c8742640beaf

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
variable {R : Type*} (A : Type*) {M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (R) (H : Type*) [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H]
variable {R H}
namespace GlobalTheory.CartierDual
theorem _root_.solution {K : Type*} [Semiring K] [Bialgebra R K] [Module.Finite R K]
    [Module.Projective R K] (f : H →ₐc[R] K) (x : A ⊗[R] CartierDual R K) :
    baseChange R A H (Bialgebra.TensorProduct.map (BialgHom.id A A) (map f) x) =
      map (Bialgebra.TensorProduct.map (BialgHom.id A A) f) (baseChange R A K x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a φ =>
    refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => ?_)
    simp
end GlobalTheory.CartierDual
