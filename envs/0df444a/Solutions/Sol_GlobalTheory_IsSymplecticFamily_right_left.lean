-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.right_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:51.908387+00:00
-- url     : https://prove2.me/submissions/243fddbf-5831-4858-b9ae-341851c8f0a7

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
theorem _root_.solution [DecidableEq ι] (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) (i j : ι) :
    B (f i) (e j) = if i = j then -d i else 0 := by
  rw [← hB.neg_eq, h.left_right]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]
end GlobalTheory.IsSymplecticFamily
