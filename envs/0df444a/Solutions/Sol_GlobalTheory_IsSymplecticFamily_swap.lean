-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:12.722787+00:00
-- url     : https://prove2.me/submissions/81f208dd-52c3-47ab-b46d-9b14c3a8dce4

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
open GlobalTheory.IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}
namespace GlobalTheory.IsSymplecticFamily
theorem _root_.solution (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) : IsSymplecticFamily (-B) f e d where
  left_left i j := by simp [h.right_right]
  right_right i j := by simp [h.left_left]
  left_right_self i := by simp [hB.neg_eq, h.left_right_self]
  left_right_ne i j hij := by simp [hB.neg_eq, h.left_right_ne j i hij.symm]
end GlobalTheory.IsSymplecticFamily
