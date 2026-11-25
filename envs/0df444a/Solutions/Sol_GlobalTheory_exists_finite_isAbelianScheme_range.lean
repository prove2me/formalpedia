-- Prove2me | solution 1 for GlobalTheory.exists_finite_isAbelianScheme_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:38.672572+00:00
-- url     : https://prove2.me/submissions/375c8182-17d8-4914-bb0c-22526a689799

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteIsAbelianSchemeDescends
import Theorems.Thm_GlobalTheory_FieldModel_exists_baseChange
import Theorems.Thm_GlobalTheory_FieldModel_exists_factor
import Theorems.Thm_GlobalTheory_FieldModel_hasModel
import Theorems.Thm_GlobalTheory_FieldModel_isPullback_sq
import Theorems.Thm_GlobalTheory_FieldModel_isPullback_unit
import Theorems.Thm_GlobalTheory_FieldModel_spMap_comp
import Theorems.Thm_GlobalTheory_FieldModel_sq_comp
import Theorems.Thm_GlobalTheory_FieldModel_sq_fst
import Theorems.Thm_GlobalTheory_FieldModel_sq_snd
import Theorems.Thm_GlobalTheory_T_group_structure_descends_along_pullback
import Theorems.Thm_GlobalTheory_T_hom_descends_to_subfield_containing_finset_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.FieldModel
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (β : k₁ →+* K), s ⊆ Set.range β →
      ∃ (B₁ : Over (Sp k₁)) (_ : GrpObj B₁) (φ : B.left ⟶ B₁.left),
        IsAbelianScheme B₁ ∧ IsGrpPullback B B₁ (spMap β) φ := by
  have := hB.proper
  obtain ⟨s₀, hs₀⟩ := hasModel B
  let k₀ := Subfield.closure (s₀ : Set K)
  obtain ⟨B₀, φ₀, H₀⟩ := hs₀ k₀ k₀.subtype fun x hx => ⟨⟨x, Subfield.subset_closure hx⟩, rfl⟩
  have lB : LocallyOfFiniteType B.hom := inferInstance
  have pBB : IsProper (B ⊗ B).hom := inferInstanceAs (IsProper (pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨sm, hm⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ (isPullback_sq H₀) H₀ inferInstance inferInstance lB μ[B]
  obtain ⟨si, hi⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ H₀ H₀ inferInstance inferInstance lB ι[B]
  obtain ⟨se, he⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ (isPullback_unit _) H₀
    (inferInstanceAs (QuasiCompact (𝟙 (Sp K)))) (inferInstanceAs (QuasiSeparated (𝟙 (Sp K)))) lB η[B]
  refine ⟨s₀ ∪ (sm ∪ (si ∪ se)), by simp, fun k₁ _ β hs => ?_⟩
  simp only [Set.union_subset_iff] at hs
  obtain ⟨b₀, bm, bi, be⟩ := hs
  obtain ⟨ρ, hρ⟩ := exists_factor β (s₀ : Set K) b₀
  obtain ⟨φ₁, eφ, H₁⟩ := exists_baseChange (spMap_comp hρ) H₀
  have P₁ : IsPullback (pullback.fst B₀.hom (spMap ρ)) ((Over.pullback (spMap ρ)).obj B₀).hom B₀.hom (spMap ρ) :=
    .of_hasPullback _ _
  obtain ⟨m₁, hm₁⟩ := hm k₁ ρ β hρ bm _ _ (sq H₁.w) _ φ₁ _ (isPullback_sq P₁) P₁ (sq_comp eφ _ _ _) eφ
    (isPullback_sq H₁).w H₁.w
  obtain ⟨i₁, hi₁⟩ := hi k₁ ρ β hρ bi _ _ φ₁ _ φ₁ _ P₁ P₁ eφ eφ H₁.w H₁.w
  obtain ⟨e₁, he₁⟩ := he k₁ ρ β hρ be (𝟙_ _) _ (spMap β) _ φ₁ _ (isPullback_unit (spMap ρ)) P₁ (spMap_comp hρ) eφ
    (isPullback_unit (spMap β)).w H₁.w
  obtain ⟨gB, ab, gpB⟩ := GlobalTheory.T.group_structure_descends_along_pullback k₁ K β B _ φ₁ hB H₁ m₁ i₁ e₁ _ (sq_fst _) (sq_snd _) hm₁ hi₁ he₁
  exact ⟨_, gB, φ₁, ab, gpB⟩
end GlobalTheory
