-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.orthogonal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:59.262025+00:00
-- url     : https://prove2.me/submissions/21ff940c-f99d-44d0-90c0-03de8285c1d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_orthogonal_iff
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
omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R M]
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution {ι κ : Type*} [Finite ι] [Finite κ]
    {b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) R M} (hb : IsSymplecticBasis B b) {v : Basis ι R I}
    (hv : ∀ i, b (Sum.inl (Sum.inl i)) = v i) :
    B.orthogonal I = Submodule.span R
      (Set.range (fun i => b (Sum.inl i)) ∪ Set.range fun k => b (Sum.inr (Sum.inr k))) := by
  have : (Set.range (fun i => b (Sum.inl i)) ∪ Set.range fun k => b (Sum.inr (Sum.inr k))) =
      b '' (Set.range fun i => Sum.inr (Sum.inl i))ᶜ := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨_, by simp, rfl⟩
      · exact ⟨_, by simp, rfl⟩
    · rintro ⟨i | i | i, hi, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact absurd ⟨i, rfl⟩ hi
      · exact Or.inr ⟨i, rfl⟩
  ext x
  rw [this, hb.mem_orthogonal_iff hv, Basis.mem_span_image]
  constructor
  · rintro h j hj ⟨i, rfl⟩
    exact Finsupp.mem_support_iff.1 hj (h i)
  · intro h i
    by_contra hne
    exact h (Finsupp.mem_support_iff.2 hne) ⟨i, rfl⟩
end IsSymplecticBasis
end GlobalTheory
