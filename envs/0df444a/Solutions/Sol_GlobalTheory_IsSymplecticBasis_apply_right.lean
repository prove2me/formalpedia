-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.apply_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:57.400502+00:00
-- url     : https://prove2.me/submissions/1404c055-8f0c-482a-929a-42edd78240dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_right

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
theorem _root_.solution [Finite ι] (h : IsSymplecticBasis B b) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) := by
  simpa using IsSymplecticBasisOfType.apply_right h x k
end GlobalTheory.IsSymplecticBasis
