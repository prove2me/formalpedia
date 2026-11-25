-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.derivLeft_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:18.453659+00:00
-- url     : https://prove2.me/submissions/ab10e7f4-ce66-4f6b-aeef-3732a1836cc4

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
    derivLeft φ hφ y =
      TensorProduct.lid k H (LinearMap.rTensor H φ (Coalgebra.comul (R := k) y)) := rfl
end GlobalTheory.LeftRightDerivations
