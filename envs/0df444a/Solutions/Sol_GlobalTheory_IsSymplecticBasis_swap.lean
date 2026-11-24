-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:10.459801+00:00
-- url     : https://prove2.me/submissions/66ebd206-da3f-4556-a80c-1aeb33aa3f5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_swap
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_swap

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
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}
open GlobalTheory.IsSymplecticBasis
variable {b : Basis (ι ⊕ ι) R M}
namespace GlobalTheory.IsSymplecticBasis
theorem _root_.solution (h : IsSymplecticBasis B b) (hB : B.IsAlt) :
    IsSymplecticBasis (-B) (b.reindex (Equiv.sumComm ι ι)) :=
  IsSymplecticBasisOfType.swap h hB
end GlobalTheory.IsSymplecticBasis
