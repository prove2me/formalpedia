-- Prove2me | solution 1 for GlobalTheory.orthogonalQuotientForm_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:27.6771+00:00
-- url     : https://prove2.me/submissions/7556d9c6-3be3-4fab-aa6a-0e45c80566e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (I : Submodule R M) (x y : B.orthogonal I) :
    orthogonalQuotientForm B hB I (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B x y := rfl
end GlobalTheory
