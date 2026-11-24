-- Prove2me | solution 1 for GlobalTheory.CartierDual.pointsEquiv_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:33.128799+00:00
-- url     : https://prove2.me/submissions/3fdacc65-bd93-45fd-887a-2db622c4def5

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
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Module.Finite R C] [Module.Projective R C]
variable {A : Type*} [CommSemiring A] [Algebra R A]
namespace GlobalTheory.CartierDual
theorem _root_.solution (f : CartierDual R C →ₐ[R] A) (x : A ⊗[R] C) :
    (pointsEquiv R C A f).val = x ↔ ∀ φ, tensorToHom R A C x φ = f φ :=
  ⟨fun h φ => h ▸ tensorToHom_pointsEquiv f φ,
    fun h => eq_of_forall_tensorToHom fun φ => by rw [h, tensorToHom_pointsEquiv]⟩
end GlobalTheory.CartierDual
