-- Prove2me | solution 1 for GlobalTheory.isTorsionFree_quotient_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:59.69786+00:00
-- url     : https://prove2.me/submissions/56440c8a-7792-4684-a73f-46f9f3c7307e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_isTorsionFree_quotient_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk

set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [IsDomain R] (B : LinearMap.BilinForm R M)
    (I : Submodule R M) : IsTorsionFree R (M ⧸ B.orthogonal I) :=
  (isTorsionFree_quotient_iff _).2 fun r x hr hx n hn => by
    simpa [hr] using hx n hn
end GlobalTheory
