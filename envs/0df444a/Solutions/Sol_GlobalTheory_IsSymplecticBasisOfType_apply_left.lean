-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.apply_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:14.478484+00:00
-- url     : https://prove2.me/submissions/a3b4dc0d-8312-45da-bacc-3a8830ff8401

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_left_sum
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
    B (b (Sum.inl k)) x = b.repr x (Sum.inr k) * d k := by
  have := Fintype.ofFinite ι
  have h' := IsSymplecticFamily.apply_left_sum h (b.repr x) k
  rwa [elim_eq, b.sum_repr] at h'
end GlobalTheory.IsSymplecticBasisOfType
