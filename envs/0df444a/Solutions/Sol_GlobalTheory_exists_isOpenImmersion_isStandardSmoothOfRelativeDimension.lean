-- Prove2me | solution 1 for GlobalTheory.exists_isOpenImmersion_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:35.430611+00:00
-- url     : https://prove2.me/submissions/b3b13800-c876-4000-aecb-9263897c6b62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsOpenImmersionIsStandardSmoothOfRelativeD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) :
    ∃ (B : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ B) (j : Spec B ⟶ X) (_ : IsOpenImmersion j)
      (y : Spec B), j y = x ∧ j ≫ f = Spec.map φ ∧
        φ.hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨A, j, hj, ⟨y, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have h : SmoothOfRelativeDimension (0 + d) (j ≫ f) := inferInstance
  rw [zero_add, ← hφ] at h
  obtain ⟨s, hs, h'⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).1 h
  obtain ⟨t, ht, hty⟩ : ∃ t ∈ s, t ∉ y.asIdeal := by
    by_contra hne
    push Not at hne
    exact y.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hne))
  obtain ⟨z, hz⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ t]
    exact hty
  refine ⟨.of (Localization.Away t), φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away t)),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ j, inferInstance, z,
    ?_, ?_, h' t ht⟩
  · rw [← hz]; rfl
  · rw [Category.assoc, ← hφ, Spec.map_comp]
end GlobalTheory
