-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:33.610911+00:00
-- url     : https://prove2.me/submissions/474ce00f-75cd-4fec-9f01-ca1bedceb348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_left
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
open GlobalTheory.IsSymplecticBasisOfType
variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}
namespace GlobalTheory.IsSymplecticBasisOfType
theorem _root_.solution [Fintype ι] (h : IsSymplecticBasisOfType B b d) (hB : B.IsAlt) (x y : M) :
    B x y = ∑ i, d i * (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, h.apply_left,
    ← hB.neg_eq y (b (Sum.inr _)), h.apply_right]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.IsSymplecticBasisOfType
