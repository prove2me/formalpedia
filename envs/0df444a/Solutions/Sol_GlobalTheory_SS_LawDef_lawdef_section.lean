-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.lawdef_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:47.856795+00:00
-- url     : https://prove2.me/submissions/0af9c5eb-7f96-433b-99d4-d2ab11dfe6f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_global
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_comp
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_comp_all
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_lift
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_twist
import Theorems.Thm_GlobalTheory_SS_LawDef_isOpen_isoAt
import Theorems.Thm_GlobalTheory_SS_LawDef_sec_lift
import Theorems.Thm_GlobalTheory_SS_LawDef_map_modelSectionSpecialPoint_comp
import Theorems.Thm_GlobalTheory_SS_LawDef_modelSectionSpecialPoint_mem_specialFibre
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_comp_sec
import Theorems.Thm_GlobalTheory_SS_LawDef_isPullback_fibre_fst
import Theorems.Thm_GlobalTheory_SS_LawDef_isPullback_fibre_snd
import Theorems.Thm_GlobalTheory_SS_LawDef_exists_fibre
import Theorems.Thm_GlobalTheory_SS_LawDef_exists_section_general
import Theorems.Thm_GlobalTheory_SS_GI_defAt_comp
import Theorems.Thm_GlobalTheory_SS_GI_defAt_twist
import Theorems.Thm_GlobalTheory_SS_GI_isOpen_isoAt
import Theorems.Thm_GlobalTheory_SS_IsoAt_defAt
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_translation_by_section
import Theorems.Thm_GlobalTheory_T_modelMapGenericallyOpenImmersion_calculus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsLocalRing R]
namespace GlobalTheory.SS.LawDef
theorem _root_.solution [IsDomain R] (hR : SH R K) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : Model R A) (hM : Strict M) (X Y : 𝟙_ (Over (Sp R)) ⟶ M.Y) :
    ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧
      DefAt (M.prod M) (M.twist (transl a)) (μ[A]) (sp0 (lift X Y)) := by
  have := hR.2.2.2
  obtain ⟨x, hx, -, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM X
  obtain ⟨y, hy, gy, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM Y
  have gφ := (GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hR).2.1 A A A M M M _ _ hM.1.1 hM.1.2.2 gy
  obtain ⟨z₁, hz₁, i₁⟩ := (hM.2 false _ (modelSectionSpecialPoint_mem_specialFibre M Y)).2
  obtain ⟨z₂, hz₂, i₂⟩ := (hM.2 true _ (modelSectionSpecialPoint_mem_specialFibre M X)).1
  obtain ⟨u₁, m₁, rfl⟩ := exists_fibre (isPullback_fibre_snd (Z := M.Y) Y) z₁ hz₁
  obtain ⟨u₂, m₂, rfl⟩ := exists_fibre (isPullback_fibre_fst (Z := M.Y) X) z₂ hz₂
  obtain ⟨s, hs, hs'⟩ := exists_section_general hR hM.1.1 gφ
    ((isOpen_isoAt (M.prod M) (M.prod M) (shear A false)).preimage (lift (𝟙 M.Y) (toUnit M.Y ≫ Y)).left.continuous)
    ((isOpen_isoAt (M.prod M) (M.prod M) (shear A true)).preimage (lift (toUnit M.Y ≫ X) (𝟙 M.Y)).left.continuous)
    ⟨u₁, m₁, i₁⟩ ⟨u₂, m₂, i₂⟩
  obtain ⟨a, ha, ga, ha'⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM s
  obtain ⟨t, ht, ht'⟩ := hs' a ha
  have u1 : ∀ (w : 𝟙_ (Over (Sp R)) ⟶ M.Y), w ≫ toUnit M.Y = 𝟙 _ := fun w => toUnit_unique _ _
  have u2 : ∀ (w : 𝟙_ (Over (Sp K)) ⟶ A), w ≫ toUnit A = 𝟙 _ := fun w => toUnit_unique _ _
  have d1 : DefAt M M (transl a).inv (sp0 Y) := by
    refine (ha' (sp0 Y) false ?_).defAt
    have e : s ≫ lift (𝟙 M.Y) (toUnit M.Y ≫ Y) = Y ≫ lift (toUnit M.Y ≫ s) (𝟙 M.Y) := by
      ext1 <;> simp [reassoc_of% u1]
    rw [map_modelSectionSpecialPoint_comp, ← e, ← map_modelSectionSpecialPoint_comp]
    exact hs
  have d2 : DefAt (M.prod M) (M.prod M) (shear A true) (sp0 (lift X t)) := by
    have e : t ≫ lift (toUnit M.Y ≫ X) (𝟙 M.Y) = lift X t := by
      ext1 <;> simp [reassoc_of% u1]
    rw [← e, ← map_modelSectionSpecialPoint_comp]
    exact IsoAt.defAt ht'
  have ef := defAt_global (M.prod M) M _ _ (prod_j_fst M M)
  have es := defAt_global (M.prod M) M _ _ (prod_j_snd M M)
  have d3 : DefAt (M.prod M) M (snd A A ≫ (transl a).inv) (sp0 (lift X Y)) := by
    refine defAt_comp es ⟨sp0 (lift X Y), trivial⟩ ?_
    have : ((⊤ : (M.prod M).Y.left.Opens).ι ≫ (snd M.Y M.Y).left) ⟨sp0 (lift X Y), trivial⟩ = sp0 Y := by
      rw [Scheme.Hom.comp_apply]
      exact (map_modelSectionSpecialPoint_comp (lift X Y) (snd M.Y M.Y)).trans (by rw [lift_snd])
    rw [this]; exact d1
  have d4 := defAt_lift (⟨⊤, _, trivial, ef⟩ : DefAt (M.prod M) M (fst A A) (sp0 (lift X Y))) d3
  have e5 : lift x y ≫ lift (fst A A) (snd A A ≫ (transl a).inv) = lift x (a ≫ ι[A] ≫ (transl y).hom) := by
    ext1
    · simp
    · have : a ≫ ι[A] = a⁻¹ := rfl
      simp only [Category.assoc, lift_snd, lift_snd_assoc, ← Category.assoc a, this]
      simp only [transl, MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% u2, Category.comp_id]
      exact _root_.mul_comm _ _
  have d5 := defAt_comp_sec (sec_lift hx hy) (by rw [e5]; exact sec_lift hx ht) d4 d2
  have d6 := defAt_comp_all d5 (fun w => (⟨⊤, _, trivial, es⟩ : DefAt (M.prod M) M (snd A A) w))
  refine ⟨a, ga, defAt_twist _ ?_⟩
  convert d6 using 1
  have hμ : μ[A] = fst A A * snd A A := by
    rw [Hom.mul_def]; simp
  have u3 : ∀ (w : A ⊗ A ⟶ A), w ≫ toUnit A = toUnit _ := fun w => toUnit_unique _ _
  simp only [shear, transl, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, reassoc_of% u3,
    Category.comp_id]
  rw [hμ, _root_.mul_left_comm]
end GlobalTheory.SS.LawDef
