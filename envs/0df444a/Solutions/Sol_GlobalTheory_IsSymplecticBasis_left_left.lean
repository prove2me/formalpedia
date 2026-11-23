-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.left_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:27.703199+00:00
-- url     : https://prove2.me/submissions/3189f616-a776-452d-8496-cdda7b4369d0

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
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}
open GlobalTheory.IsSymplecticBasis
variable {b : Basis (ι ⊕ ι) R M}
namespace GlobalTheory.IsSymplecticBasis
theorem _root_.solution (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inl j)) = 0 := IsSymplecticFamily.left_left h i j
end GlobalTheory.IsSymplecticBasis
