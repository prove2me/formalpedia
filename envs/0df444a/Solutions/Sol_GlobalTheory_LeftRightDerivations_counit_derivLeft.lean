-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.counit_derivLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:09.788809+00:00
-- url     : https://prove2.me/submissions/d217af2c-7dbd-4d88-93b7-c9acb75a1bfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
import Theorems.Thm_GlobalTheory_LeftRightDerivations_counit_contrLeft

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
    Coalgebra.counit (R := k) (derivLeft φ hφ y) = φ y := by
  have h : derivLeft φ hφ y = contrLeft φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrLeft, contrRight_counit_comul]
end GlobalTheory.LeftRightDerivations
