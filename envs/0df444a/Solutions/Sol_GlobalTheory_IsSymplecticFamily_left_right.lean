-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.left_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:27.661837+00:00
-- url     : https://prove2.me/submissions/1d0535d8-c4e1-4e4c-af59-e761ed422332

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
theorem _root_.solution [DecidableEq ι] (h : IsSymplecticFamily B e f d) (i j : ι) :
    B (e i) (f j) = if i = j then d i else 0 := by
  split_ifs with hij
  · subst hij; exact h.left_right_self i
  · exact h.left_right_ne i j hij
end GlobalTheory.IsSymplecticFamily
