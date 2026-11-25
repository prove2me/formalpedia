-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.exists_free_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:10:30.514751+00:00
-- url     : https://prove2.me/submissions/02985da6-c64c-46d2-8519-19a9f281a59a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom
import Theorems.Thm_GlobalTheory_SplitFinitePart_range_of_isPullback
import Theorems.Thm_GlobalTheory_SplitFinitePart_exists_free_away

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π]
    [LocallyOfFinitePresentation π] (p : PrimeSpectrum R) (W W' : (Sp R).Opens) (H : Z.Opens)
    (ρ : H.toScheme ⟶ W.toScheme) (hW : p ∈ W) (hW' : p ∈ W') (hρ : ρ ≫ W.ι = H.ι ≫ π) [IsFinite ρ] :
    ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (j : Sp B ⟶ Z), f ∉ p.asIdeal ∧
      Module.Finite (Localization.Away f) B ∧ Module.Free (Localization.Away f) B ∧ IsOpenImmersion j ∧
      j ≫ π = spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ∧
      Set.range (spMap (algebraMap R (Localization.Away f))) ⊆ (W : Set (Sp R)) ∩ W' ∧
      Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range (spMap (algebraMap R (Localization.Away f))) := by
  obtain ⟨_, ⟨f₀, rfl⟩, hp, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (W ⊓ W').1 from ⟨hW, hW'⟩) (W ⊓ W').isOpen
  let A := Localization.Away f₀
  have hA : Set.range (spMap (algebraMap R A)) ⊆ (W : Set (Sp R)) ∩ W' :=
    (PrimeSpectrum.localization_away_comap_range A f₀).subset.trans hsub
  have hA' : Set.range (spMap (algebraMap R A)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact fun x hx => (hA hx).1
  let a := IsOpenImmersion.lift W.ι (spMap (algebraMap R A)) hA'
  have ha : a ≫ W.ι = spMap (algebraMap R A) := IsOpenImmersion.lift_fac _ _ _
  have P₀ : IsPullback (𝟙 _) ρ (H.ι ≫ π) W.ι := IsPullback.of_horiz_isIso_mono ⟨by rw [hρ, Category.id_comp]⟩
  have : Flat ρ := MorphismProperty.of_isPullback (P := @Flat) P₀ inferInstance
  have : LocallyOfFinitePresentation ρ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) P₀ inferInstance
  have : IsAffine (pullback ρ a) := isAffine_of_isAffineHom (pullback.snd ρ a)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a)
  let B₀ : Type := Γ(pullback ρ a, ⊤)
  letI : Algebra A B₀ := ψ.hom.toAlgebra
  have : Module.Finite A B₀ := (IsFinite.SpecMap_iff ψ).mp (by rw [hψ]; infer_instance)
  have : Module.Flat A B₀ := Flat.SpecMap_iff.mp (show Flat (Spec.map ψ) by rw [hψ]; infer_instance)
  have : Algebra.FinitePresentation A B₀ := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    (show LocallyOfFinitePresentation (Spec.map ψ) by rw [hψ]; infer_instance)
  obtain ⟨f, _, hf, hT, hfree⟩ := exists_free_away f₀ p hp B₀
  let A' := Localization.Away f
  have e : spMap (algebraMap A A') ≫ spMap (algebraMap R A) = spMap (algebraMap R A') := by
    rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R A A']; rfl
  have P₁ := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A A' B₀)
  have P₂ : IsPullback ((pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) (spMap (algebraMap A B₀)) ρ a := by
    have h : spMap (algebraMap A B₀) = (pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a := hψ
    rw [h]
    exact IsPullback.of_iso (IsPullback.of_hasPullback ρ a) (pullback ρ a).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have P₃ := P₁.flip.paste_horiz P₂
  have e' : (spMap (algebraMap A A') ≫ a) ≫ W.ι = spMap (algebraMap R A') := by rw [Category.assoc, ha, e]
  have : IsOpenImmersion (spMap (algebraMap R A')) := IsOpenImmersion.of_isLocalization f
  have : IsOpenImmersion ((spMap (algebraMap A A') ≫ a) ≫ W.ι) := by rw [e']; infer_instance
  have ho : IsOpenImmersion (spMap (algebraMap A A') ≫ a) := IsOpenImmersion.of_comp _ W.ι
  have ho' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) P₃.flip ho
  have hr := range_of_isPullback P₃
  have hw := P₃.w
  generalize (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B₀)).toRingHom) ≫
    (pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) = j at ho' hr hw
  have hρ' : ∀ z, (ρ z).1 = π z.1 := fun z => congrArg (fun φ : H.toScheme ⟶ _ => φ z) hρ
  refine ⟨f, A' ⊗[A] B₀, inferInstance, inferInstance, j ≫ H.ι, hf, inferInstance, hfree, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, reassoc_of% hw, ← e']
    rfl
  · rintro _ ⟨y, rfl⟩
    exact hA ⟨spMap (algebraMap A A') y, by rw [← Scheme.Hom.comp_apply, e]⟩
  · ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨w, hw'⟩ := hr.subset ⟨y, rfl⟩
      refine ⟨(j y).2, w, ?_⟩
      rw [← e', Scheme.Hom.comp_apply, hw']
      exact hρ' _
    · rintro ⟨hz, w, hw'⟩
      obtain ⟨y, hy⟩ := hr.superset (show (⟨z, hz⟩ : H.toScheme) ∈ ρ ⁻¹' Set.range (spMap (algebraMap A A') ≫ a) from
        ⟨w, Subtype.ext (by
          refine Eq.trans ?_ (hρ' ⟨z, hz⟩).symm
          refine Eq.trans ?_ hw'
          rw [← e']; rfl)⟩)
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]; rfl⟩
end GlobalTheory.SplitFinitePart
