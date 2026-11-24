-- Prove2me | solution 1 for GlobalTheory.CartierDual.comul_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:30.33093+00:00
-- url     : https://prove2.me/submissions/344ce0cd-affa-4dc9-9689-f8cfc88a32dc

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
variable {R H : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Module.Finite R H]
  [Module.Projective R H]
namespace GlobalTheory.CartierDual
theorem _root_.solution (φ : CartierDual R H) (x : CartierDual R H ⊗[R] CartierDual R H) :
    comul φ = x ↔ ∀ a b, pair R H H x (a ⊗ₜ b) = φ (a * b) :=
  ⟨fun h a b => h ▸ pair_comul_tmul φ a b,
    fun h => tensor_ext fun a b => by rw [pair_comul_tmul, h]⟩
end GlobalTheory.CartierDual
