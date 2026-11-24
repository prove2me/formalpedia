-- Prove2me | solution 1 for GlobalTheory.CartierDual.counit_addMonoidAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:31.115997+00:00
-- url     : https://prove2.me/submissions/8dc0dfcc-ae95-43cc-a7b1-3eb43a10b441

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
variable (R Γ : Type*) [CommSemiring R]
variable {R Γ}
namespace GlobalTheory.CartierDual
theorem _root_.solution [AddMonoid Γ] [Finite Γ]
    (φ : CartierDual R (AddMonoidAlgebra R Γ)) :
    counit (R := R) φ = addMonoidAlgebraEquiv R Γ φ 0 := by
  rw [addMonoidAlgebraEquiv_apply]; rfl
end GlobalTheory.CartierDual
