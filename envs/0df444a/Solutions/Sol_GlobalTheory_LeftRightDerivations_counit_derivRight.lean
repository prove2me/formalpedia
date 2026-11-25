-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.counit_derivRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:13.273865+00:00
-- url     : https://prove2.me/submissions/b25a97c4-ab64-4618-8a15-2b9fb5d468c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
import Theorems.Thm_GlobalTheory_LeftRightDerivations_counit_contrRight

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
    Coalgebra.counit (R := k) (derivRight φ hφ y) = φ y := by
  have h : derivRight φ hφ y = contrRight φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrRight, contrLeft_counit_comul]
end GlobalTheory.LeftRightDerivations
