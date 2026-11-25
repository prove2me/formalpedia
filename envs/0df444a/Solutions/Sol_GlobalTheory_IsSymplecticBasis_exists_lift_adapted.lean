-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.exists_lift_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:23.419811+00:00
-- url     : https://prove2.me/submissions/fb47ab59-2077-457f-99c3-dfbc5619099a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_iff_repr_inr
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_iff_repr_inl
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_span_inl_eq
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_span_inr_eq
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_adapted
import Theorems.Thm_GlobalTheory_repr_semilinear_of_map_basis
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_lift
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R Λ M l : Type*} [CommRing S] [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup Λ] [Module S Λ] [AddCommGroup M] [Module R M] [Fintype l]
  {f : S →+* R} {B : LinearMap.BilinForm S Λ} {B' : LinearMap.BilinForm R M}
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution (hf : Surjective f) (hB : B.IsAlt) (hB' : B'.IsAlt)
    (φ : Λ →ₛₗ[f] M) {b : Basis (l ⊕ l) S Λ} {b' : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hb' : IsSymplecticBasis B' b') (h : ∀ i, φ (b i) = b' i)
    {P Q : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B' x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B' x y = 0) (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧
      Submodule.span R (Set.range fun i => φ (c (.inl i))) = P ∧
      Submodule.span R (Set.range fun i => φ (c (.inr i))) = Q ∧
      (∀ x, φ x ∈ P ↔ ∀ i, f (c.repr x (.inr i)) = 0) ∧
      ∀ x, φ x ∈ Q ↔ ∀ i, f (c.repr x (.inl i)) = 0 := by
  obtain ⟨c', hc', h₁, h₂⟩ := hb'.exists_adapted hB' hP hQ hPQ
  obtain ⟨c, hc, hcc⟩ := hb.exists_lift hf hB hB' φ hb' h hc'
  refine ⟨c, hc, ?_, ?_, fun x => ?_, fun x => ?_⟩
  · simpa only [hcc] using hc'.span_inl_eq hP h₁
  · simpa only [hcc] using hc'.span_inr_eq hQ h₂
  · simp only [hc'.mem_iff_repr_inr hP h₁, repr_semilinear_of_map_basis φ hcc]
  · simp only [hc'.mem_iff_repr_inl hQ h₂, repr_semilinear_of_map_basis φ hcc]
end IsSymplecticBasis
end GlobalTheory
