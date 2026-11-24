-- Prove2me | solution 1 for GlobalTheory.CartierDual.isPrimitiveElem_iff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:38.164693+00:00
-- url     : https://prove2.me/submissions/dbe4869d-0f36-4e64-949c-9939273555ab

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
variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H]
namespace GlobalTheory.CartierDual
theorem _root_.solution (a : H) : IsPrimitiveElem R a ↔
    ∀ φ ψ : CartierDual R H, (φ * ψ) a = φ 1 * ψ a + ψ 1 * φ a := by
  refine ⟨fun h φ ψ => ?_, fun h => tensor_eq_of_forall_pair fun φ ψ => ?_⟩
  · rw [mul_apply, h]; simp [mul_comm, add_comm]
  · rw [← mul_apply, h]; simp [mul_comm, add_comm]
end GlobalTheory.CartierDual
