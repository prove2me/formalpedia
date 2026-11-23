-- Prove2me | solution 1 for GlobalTheory.isTorsionFree_quotient_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:43.273634+00:00
-- url     : https://prove2.me/submissions/69df77f5-9cf4-4a76-8e94-1f5889489a33

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [IsDomain R] (I : Submodule R M) :
    IsTorsionFree R (M ⧸ I) ↔ ∀ (r : R) (x : M), r ≠ 0 → r • x ∈ I → x ∈ I := by
  rw [isTorsionFree_iff_smul_eq_zero]
  constructor
  · intro h r x hr hx
    have := h r (Submodule.Quotient.mk x)
      (by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hx)
    simpa [hr] using this
  · intro h r x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((Submodule.Quotient.mk_eq_zero _).2 (h r x hr hx))
end GlobalTheory
