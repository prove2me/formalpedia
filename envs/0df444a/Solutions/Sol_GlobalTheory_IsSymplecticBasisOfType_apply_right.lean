-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.apply_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:14.588245+00:00
-- url     : https://prove2.me/submissions/3000fe71-87c4-45d5-86fe-966c1c2b31d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_sum_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_elim_eq

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
open GlobalTheory.IsSymplecticBasisOfType
variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}
namespace GlobalTheory.IsSymplecticBasisOfType
theorem _root_.solution [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) * d k := by
  have := Fintype.ofFinite ι
  have h' := IsSymplecticFamily.apply_sum_right h (b.repr x) k
  rwa [elim_eq, b.sum_repr] at h'
end GlobalTheory.IsSymplecticBasisOfType
