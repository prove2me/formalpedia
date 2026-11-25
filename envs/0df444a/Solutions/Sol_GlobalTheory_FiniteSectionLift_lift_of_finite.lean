-- Prove2me | solution 1 for GlobalTheory.FiniteSectionLift.lift_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:37.888277+00:00
-- url     : https://prove2.me/submissions/1d5003b5-6795-4e01-9dec-66e3b1611c3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionOfFinite
import Theorems.Thm_GlobalTheory_FiniteSectionLift_exists_section_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FiniteSectionLift
namespace GlobalTheory.FiniteSectionLift
theorem _root_.solution : ∀ (R K : CommRingCat) (φ : R ⟶ K),
    Function.Injective (⇑(CommRingCat.Hom.hom φ) : (↑R : Type) → (↑K : Type)) →
    (∀ (x : (↑K : Type)), RingHom.IsIntegralElem (CommRingCat.Hom.hom φ) x →
      ∃ (r : (↑R : Type)), (CommRingCat.Hom.hom φ : (↑R : Type) → (↑K : Type)) r = x) →
    ∀ (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : AlgebraicGeometry.Spec R ⟶ P)
      (y : AlgebraicGeometry.Spec K ⟶ Z), AlgebraicGeometry.IsFinite p →
      CategoryTheory.CategoryStruct.comp y p =
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ₀ →
      ∃ (ξ : AlgebraicGeometry.Spec R ⟶ Z),
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ = y ∧
        CategoryTheory.CategoryStruct.comp ξ p = ξ₀ := by
  intro R K φ hinj hint Z P p ξ₀ y hp hy
  haveI : IsAffine (pullback p ξ₀) := isAffine_of_isAffineHom (pullback.snd p ξ₀)
  let l : Spec K ⟶ pullback p ξ₀ := pullback.lift y (Spec.map φ) hy
  let g : R ⟶ Γ(pullback p ξ₀, ⊤) :=
    Spec.preimage ((pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀)
  let f : Γ(pullback p ξ₀, ⊤) ⟶ K := Spec.preimage (l ≫ (pullback p ξ₀).isoSpec.hom)
  have hgS : Spec.map g = (pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀ := Spec.map_preimage _
  have hfS : Spec.map f = l ≫ (pullback p ξ₀).isoSpec.hom := Spec.map_preimage _
  have hgfin : g.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hgS]
    infer_instance
  have hf : g ≫ f = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hfS, hgS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_section_of_finite R _ K φ hinj hint g hgfin f hf
  refine ⟨Spec.map s ≫ (pullback p ξ₀).isoSpec.inv ≫ pullback.fst p ξ₀, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hs2, hfS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd p ξ₀),
      ← hgS, ← Category.assoc, ← Spec.map_comp, hs1, Spec.map_id, Category.id_comp]
end GlobalTheory.FiniteSectionLift
