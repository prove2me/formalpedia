-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.mem_orthogonal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:41.962795+00:00
-- url     : https://prove2.me/submissions/80e4725e-8cb7-4393-9100-fc758fec950d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_left
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
omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R M]
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution {ι κ : Type*} [Finite ι] [Finite κ]
    {b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) R M} (hb : IsSymplecticBasis B b) {v : Basis ι R I}
    (hv : ∀ i, b (Sum.inl (Sum.inl i)) = v i) (x : M) :
    x ∈ B.orthogonal I ↔ ∀ i, b.repr x (Sum.inr (Sum.inl i)) = 0 := by
  constructor
  · intro hx i
    rw [← hb.apply_left, hv]
    exact hx _ (v i).2
  · intro hx n hn
    have : (B.flip x) ∘ₗ I.subtype = 0 := v.ext fun i => by
      simp [← hv, hb.apply_left, hx]
    exact LinearMap.congr_fun this ⟨n, hn⟩
end IsSymplecticBasis
end GlobalTheory
