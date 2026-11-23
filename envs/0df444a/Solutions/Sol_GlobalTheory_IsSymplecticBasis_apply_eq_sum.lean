-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:08.374863+00:00
-- url     : https://prove2.me/submissions/1e5306b4-1b4a-4b03-a984-59f7ca67d77f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum

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
theorem _root_.solution [Fintype ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) (x y : M) :
    B x y = ∑ i, (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) := by
  simpa using IsSymplecticBasisOfType.apply_eq_sum h hB x y
end GlobalTheory.IsSymplecticBasis
