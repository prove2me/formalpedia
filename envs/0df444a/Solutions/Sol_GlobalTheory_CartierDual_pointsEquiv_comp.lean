-- Prove2me | solution 1 for GlobalTheory.CartierDual.pointsEquiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:47.553361+00:00
-- url     : https://prove2.me/submissions/4ca0588d-ff9e-4d1e-a0d3-fd9145158a3e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_CartierDual_pointsEquiv_eq_iff

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
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Module.Finite R C] [Module.Projective R C]
variable {A : Type*} [CommSemiring A] [Algebra R A]
namespace GlobalTheory.CartierDual
theorem _root_.solution {B : Type*} [CommSemiring B] [Algebra R B] (g : A →ₐ[R] B)
    (f : CartierDual R C →ₐ[R] A) :
    (pointsEquiv R C B (g.comp f)).val =
      LinearMap.rTensor C g.toLinearMap (pointsEquiv R C A f).val :=
  (pointsEquiv_eq_iff _ _).2 fun φ => by
    rw [LinearMap.rTensor, tensorToHom_map, tensorToHom_pointsEquiv]; rfl
end GlobalTheory.CartierDual
