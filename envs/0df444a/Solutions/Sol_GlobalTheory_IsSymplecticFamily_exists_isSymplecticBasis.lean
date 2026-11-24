-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.exists_isSymplecticBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:42.905935+00:00
-- url     : https://prove2.me/submissions/bd80d86a-6009-4e9a-86d6-f65d5ddb1cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_linearIndependent
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_isUnit
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right

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
namespace GlobalTheory
namespace IsSymplecticFamily
theorem _root_.solution [IsDomain R] [Finite ι] {e f : ι → M}
    {d : ι → R} (h : IsSymplecticFamily B e f d) (hd : ∀ i, d i ≠ 0)
    (hspan : Submodule.span R (Set.range (Sum.elim e f)) = ⊤) (hp : Surjective B) :
    ∃ b : Basis (ι ⊕ ι) R M, IsSymplecticBasis B b ∧ ∀ i, b (Sum.inl i) = e i := by
  let b := Basis.mk (h.linearIndependent hd) hspan.ge
  have hb : IsSymplecticBasisOfType B b d := by
    simpa [IsSymplecticBasisOfType, b] using h
  choose u hu using fun k => hb.isUnit hp k
  refine ⟨b.unitsSMul (Sum.elim 1 fun k => (u k)⁻¹), ⟨fun i j => ?_, fun i j => ?_, fun i => ?_,
    fun i j hij => ?_⟩, fun i => ?_⟩
  · simp [Basis.unitsSMul_apply, b, h.left_left]
  · simp [Basis.unitsSMul_apply, b, h.right_right, Units.smul_def]
  · simp [Basis.unitsSMul_apply, b, h.left_right_self, Units.smul_def, ← hu]
  · simp [Basis.unitsSMul_apply, b, h.left_right_ne i j hij, Units.smul_def]
  · simp [Basis.unitsSMul_apply, b]
end IsSymplecticFamily
end GlobalTheory
