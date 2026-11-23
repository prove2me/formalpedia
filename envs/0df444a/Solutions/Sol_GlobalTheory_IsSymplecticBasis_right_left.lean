-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.right_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:15.11539+00:00
-- url     : https://prove2.me/submissions/1d23cd51-f9b9-42e9-b0c1-729c49664c63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left

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
theorem _root_.solution [DecidableEq ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) (i j : ι) :
    B (b (Sum.inr i)) (b (Sum.inl j)) = if i = j then -1 else 0 :=
  IsSymplecticFamily.right_left h hB i j
end GlobalTheory.IsSymplecticBasis
