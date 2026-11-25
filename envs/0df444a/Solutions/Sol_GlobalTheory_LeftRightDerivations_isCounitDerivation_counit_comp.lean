-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.isCounitDerivation_counit_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:27.261411+00:00
-- url     : https://prove2.me/submissions/9e046cef-db58-4be7-aff8-93c9538032fa

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
theorem _root_.solution (D : Derivation k H H) :
    IsCounitDerivation (Coalgebra.counit (R := k) ∘ₗ D.toLinearMap) := by

  intro a b
  simp [Derivation.leibniz, Bialgebra.counit_mul]
end GlobalTheory.LeftRightDerivations
