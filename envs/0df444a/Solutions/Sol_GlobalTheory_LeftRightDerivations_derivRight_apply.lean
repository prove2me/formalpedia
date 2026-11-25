-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.derivRight_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:23.103507+00:00
-- url     : https://prove2.me/submissions/35050ca6-1dd2-42a0-8b96-b68761572c77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LeftRightDerivations
variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]
variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]
namespace GlobalTheory.LeftRightDerivations
theorem _root_.solution (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivRight φ hφ y =
      TensorProduct.rid k H (LinearMap.lTensor H φ (Coalgebra.comul (R := k) y)) := rfl
end GlobalTheory.LeftRightDerivations
