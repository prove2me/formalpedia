-- Prove2me | solution 1 for GlobalTheory.exists_projection_of_isTorsionFree_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:56.57555+00:00
-- url     : https://prove2.me/submissions/dfdf13e3-631d-48e1-b5f9-1d76e46cb358

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk

set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}
namespace GlobalTheory
theorem _root_.solution (hI : IsTorsionFree R (M ⧸ I)) :
    ∃ p : M →ₗ[R] I, ∀ x : I, p x = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property I.mkQ LinearMap.id I.mkQ_surjective
  have hs' : ∀ y, I.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  refine ⟨LinearMap.codRestrict I (LinearMap.id - s ∘ₗ I.mkQ) fun x => ?_, fun x => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self]
  · ext
    simp [(Submodule.Quotient.mk_eq_zero I).2 x.2]
end GlobalTheory
