-- Prove2me | solution 1 for GlobalTheory.ThickGlue.exists_scheme_of_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:45:02.284004+00:00
-- url     : https://prove2.me/submissions/33148693-c362-4c5c-aeea-a32e2e24bbd4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Theorems.Thm_GlobalTheory_ThickGlue_exists_glue
import Theorems.Thm_GlobalTheory_ThickGlue_toSpec_naturality
import Theorems.Thm_GlobalTheory_ThickGlue_isClosedImmersion_toSpec
import Theorems.Thm_GlobalTheory_ThickGlue_surjective_toSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickGlue
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.ThickGlue
theorem _root_.solution : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → (∀ U ∈ 𝒰, ∀ f : Γ(B₀, U), B₀.basicOpen f ∈ 𝒰) → sSup 𝒰 = ⊤ → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (Opposite.op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (Opposite.op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (Opposite.op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (Opposite.op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (Opposite.op (B₀.basicOpen ((π.app (Opposite.op U)).hom a))))) → ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j) (φ : ∀ V : B.Opens, j ⁻¹ᵁ V ∈ 𝒰 → (Γ(B, V) ≅ 𝒜.obj (Opposite.op (j ⁻¹ᵁ V)))), (∀ V h, IsAffineOpen V ∧ (φ V h).hom ≫ π.app _ = j.app V) ∧ ∀ V V' h h' (hle : V' ≤ V), B.presheaf.map (homOfLE hle).op ≫ (φ V' h').hom = (φ V h).hom ≫ 𝒜.map (homOfLE (Scheme.Hom.preimage_mono j hle)).op := by
  intro B₀ 𝒰 haff hbo hcov 𝒜 p hp hloc
  have hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens)
      (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    rintro U hU a W rfl h
    letI := (𝒜.map (homOfLE h).op).hom.toAlgebra
    haveI := hloc U hU a
    exact IsOpenImmersion.of_isLocalization
      (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a
  have hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U) := fun U hU ↦
    isClosedImmersion_toSpec p (haff U hU) (hp U hU).1
  have hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U) := fun U hU ↦
    surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2
  have hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x) :=
    fun h x ↦ congr($(toSpec_naturality p h) x).symm
  have hopen : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V,
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    intro U hU V hV h
    have := hci V hV
    have := hsu U hU
    apply IsOpenImmersion.of_forall_source_exists
    · intro x y hxy
      obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨y, rfl⟩ := (toSpec p U).surjective y
      rw [hnat, hnat] at hxy
      rw [(B₀.homOfLE h).isOpenEmbedding.injective
        ((toSpec p V).isClosedEmbedding.injective hxy)]
    · intro x
      obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨f, hf, hxf⟩ := (haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)
      obtain ⟨a, rfl⟩ := (hp V hV).1 f
      have h1 := hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by
        have := congr($(p.naturality (homOfLE h).op).hom a)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        rw [this, Scheme.basicOpen_res]
        exact (inf_eq_right.mpr hf).symm) hf
      refine ⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩
      · rw [hnat]
        congr 1
        exact Subtype.ext (Scheme.homOfLE_apply _ _)
      · rw [← Spec.map_comp, ← 𝒜.map_comp]
        exact hloc' V hV a _ rfl (hf.trans h)
  obtain ⟨B, j, hj1, hj2, κ, hκ, h1, h2, h3⟩ := exists_glue B₀ 𝒰
    (fun U hU W x hxU hxW ↦ by
      obtain ⟨f, hf, hxf⟩ := (haff U hU).exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
      exact ⟨_, hbo U hU f, hxf, B₀.basicOpen_le f, hf⟩) hcov (specDiagram 𝒰 𝒜)
    (fun {U V} f ↦ hopen _ U.2 _ V.2 f.le) (fun U ↦ toSpec p U.1) (fun U ↦ hci _ U.2)
    (fun U ↦ hsu _ U.2) (fun h ↦ toSpec_naturality p h)
  have hV : ∀ (V : B.Opens) (h : j ⁻¹ᵁ V ∈ 𝒰), (κ ⟨_, h⟩).opensRange = V := by
    intro V h
    ext b
    obtain ⟨b, rfl⟩ := j.surjective b
    exact SetLike.ext_iff.mp (h2 ⟨_, h⟩) b
  have hle : ∀ (V : B.Opens) (h : j ⁻¹ᵁ V ∈ 𝒰), ⊤ ≤ (κ ⟨_, h⟩) ⁻¹ᵁ V := by
    intro V h x _
    have : κ ⟨_, h⟩ x ∈ (κ ⟨_, h⟩).opensRange := ⟨x, rfl⟩
    rwa [hV V h] at this
  have hiso : ∀ (V : B.Opens) (h : j ⁻¹ᵁ V ∈ 𝒰), IsIso ((κ ⟨_, h⟩).appLE V ⊤ (hle V h)) := by
    intro V h
    have := (κ ⟨_, h⟩).isIso_app V (hV V h).ge
    have : IsIso (homOfLE (hle V h)) := homOfLE_isIso_of_eq _ (top_le_iff.mp (hle V h)).symm
    rw [Scheme.Hom.appLE]
    infer_instance
  refine ⟨B, j, hj1, hj2, fun V h ↦ asIso ((κ ⟨_, h⟩).appLE V ⊤ (hle V h)) ≪≫
    Scheme.ΓSpecIso _, fun V h ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [← hV V h]
    have : IsAffine ((specDiagram 𝒰 𝒜).obj ⟨_, h⟩) := inferInstanceAs (IsAffine (Spec _))
    exact isAffineOpen_opensRange _
  · have e1 : (j ⁻¹ᵁ V).ι ≫ j = (j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩ := by
      simpa [toSpec] using h1 ⟨_, h⟩
    have hle' : ⊤ ≤ ((j ⁻¹ᵁ V).ι ≫ j) ⁻¹ᵁ V := fun x _ ↦ x.2
    have e2 : ((j ⁻¹ᵁ V).ι ≫ j).appLE V ⊤ hle' =
      ((j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩).appLE V ⊤ (e1 ▸ hle') := by
      congr 1
    rw [← cancel_mono (j ⁻¹ᵁ V).topIso.inv]
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
    refine Eq.trans ?_ (e2.symm.trans ?_)
    · simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    · rw [← Scheme.Hom.appLE_comp_appLE (j ⁻¹ᵁ V).ι j V (j ⁻¹ᵁ V) ⊤ le_rfl (fun x _ ↦ x.2),
        ← Scheme.Hom.app_eq_appLE]
      congr 1
      simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
      congr 1
  · intro V V' h h' hVV
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    have e1 := h3 (U := ⟨_, h'⟩) (V := ⟨_, h⟩) (homOfLE (Scheme.Hom.preimage_mono j hVV))
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.map_appLE_assoc, ← Category.assoc]
    congr 1
    simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact e1.symm
end GlobalTheory.ThickGlue
