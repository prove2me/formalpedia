-- Prove2me | solution 1 for GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:56.937829+00:00
-- url     : https://prove2.me/submissions/f219ee71-c4fe-41b2-97e3-a2d123173fc9

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
theorem _root_.solution (hB : B.IsAlt) (hp : Surjective B)
    (hI : IsTorsionFree R (M ⧸ I)) : B.orthogonal (B.orthogonal I) = I := by
  refine le_antisymm (fun x hx => ?_) (LinearMap.BilinForm.le_orthogonal_orthogonal hB.isRefl)
  rw [← Submodule.Quotient.mk_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_
  obtain ⟨y, hy⟩ := hp (φ ∘ₗ I.mkQ)
  have := hx y fun n hn => hB.eq_iff.1 (by
    rw [hy]; simp [(Submodule.Quotient.mk_eq_zero I).2 hn])
  rwa [hy] at this
end GlobalTheory
