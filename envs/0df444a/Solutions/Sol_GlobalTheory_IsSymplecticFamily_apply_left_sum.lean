-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.apply_left_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:53.063793+00:00
-- url     : https://prove2.me/submissions/85939d94-8bf3-4583-a625-5212304c6b07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right

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
open GlobalTheory.IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}
namespace GlobalTheory.IsSymplecticFamily
theorem _root_.solution [Fintype ι] (h : IsSymplecticFamily B e f d) (c : ι ⊕ ι → R) (k : ι) :
    B (e k) (∑ i, c i • Sum.elim e f i) = c (Sum.inr k) * d k := by
  classical
  simp [Fintype.sum_sum_type, h.left_left, h.left_right]
end GlobalTheory.IsSymplecticFamily
