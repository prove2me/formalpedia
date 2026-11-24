-- Prove2me | solution 1 for GlobalTheory.relSpec_map_isIso_over_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:23.570335+00:00
-- url     : https://prove2.me/submissions/b3251fcd-ed7e-40ae-a271-b3bd6112719c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpen
import Theorems.Thm_GlobalTheory_isIso_specMap_restrict_basicOpen_of_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option autoImplicit false
noncomputable section
open GlobalTheory
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  intro X F F' α α' hα hα' ι hαι g hg hg' V b hb W hW
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI := (relativeGluingData hα).cover.map_prop V
  haveI := (relativeGluingData hα').cover.map_prop V
  set φ := Spec.map (ι.app (Opposite.op V)) with hφ
  have hnat : (relativeGluingData hα).natTrans.app V =
      φ ≫ (relativeGluingData hα').natTrans.app V := by
    subst hαι
    simp [relativeGluingData, hφ, Spec.map_comp]
  have H : IsPullback φ ((relativeGluingData hα).cover.f V) ((relativeGluingData hα').cover.f V) g := by
    refine IsPullback.of_right ?_ (hg' V).symm ((relativeGluingData hα').isPullback_natTrans_ι_toBase V)
    rw [← hnat, hg]
    exact (relativeGluingData hα).isPullback_natTrans_ι_toBase V
  have hW' : W = (relativeGluingData hα').cover.f V ''ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) := by
    ext1; exact hW
  subst hW'
  have h1 := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H
    (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)
  have hpre : φ ⁻¹ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) =
      PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) := by
    ext x; rfl
  refine ⟨?_, ?_⟩
  · set D' : (Spec (F'.obj (Opposite.op V))).Opens := PrimeSpectrum.basicOpen b with hD'
    have H₂ := (isPullback_morphismRestrict φ D').paste_vert H
    haveI : IsIso (φ ∣_ D') := isIso_specMap_restrict_basicOpen_of_bijective _ b hb
    haveI : IsIso (pullback.snd g (D'.ι ≫ (relativeGluingData hα').cover.f V)) := by
      rw [← H₂.flip.isoPullback_inv_snd]
      infer_instance
    have hr : (D'.ι ≫ (relativeGluingData hα').cover.f V).opensRange =
        (relativeGluingData hα').cover.f V ''ᵁ D' := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      rfl
    have := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange g (D'.ι ≫ (relativeGluingData hα').cover.f V))).mpr
      (show IsIso _ from inferInstance)
    rw [hr] at this
    exact this
  · rw [← h1, hpre]
    rfl
end GlobalTheory
