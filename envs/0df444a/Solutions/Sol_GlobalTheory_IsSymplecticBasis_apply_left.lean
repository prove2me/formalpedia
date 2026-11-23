-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.apply_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:02.477555+00:00
-- url     : https://prove2.me/submissions/2320f646-0556-4d52-b507-203b31f71092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_left

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
    B (b (Sum.inl k)) x = b.repr x (Sum.inr k) := by
  simpa using IsSymplecticBasisOfType.apply_left h x k
end GlobalTheory.IsSymplecticBasis
