-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.isCounitDerivation_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:00:21.410839+00:00
-- url     : https://prove2.me/submissions/89c238b8-6ec7-4c0e-99a2-5e9b00cc9250

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
namespace GlobalTheory.LeftRightDerivations
theorem _root_.solution (φ : H →ₗ[k] k) :
    IsCounitDerivation φ ↔ ∀ a b : H, φ (a * b) =
      Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a := Iff.rfl
end GlobalTheory.LeftRightDerivations
