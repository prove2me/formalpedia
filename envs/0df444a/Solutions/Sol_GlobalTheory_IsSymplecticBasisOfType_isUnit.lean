-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:38.659943+00:00
-- url     : https://prove2.me/submissions/a403fe34-2999-4991-a8e7-42f017ca97ab

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
open GlobalTheory.IsSymplecticBasisOfType
variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}
namespace GlobalTheory.IsSymplecticBasisOfType
theorem _root_.solution [Finite ι] (h : IsSymplecticBasisOfType B b d) (hp : Surjective B) (k : ι) :
    IsUnit (d k) := by
  obtain ⟨x, hx⟩ := hp (b.coord (Sum.inr k))
  have := h.apply_right x k
  rw [hx] at this
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same] at this
  exact IsUnit.of_mul_eq_one_right _ this.symm
end GlobalTheory.IsSymplecticBasisOfType
