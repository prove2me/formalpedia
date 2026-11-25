-- Prove2me | solution 1 for GlobalTheory.FieldModel.HasModel.glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:21:26.931098+00:00
-- url     : https://prove2.me/submissions/3dc90cc3-6e35-4291-a7f5-a783723fd6fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Theorems.Thm_GlobalTheory_FieldModel_exists_factor
import Theorems.Thm_GlobalTheory_FieldModel_spMap_comp
import Theorems.Thm_GlobalTheory_FieldModel_exists_baseChange
import Theorems.Thm_GlobalTheory_T_glue_models_over_subfield
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
open GlobalTheory GlobalTheory.FieldModel
variable {K : Type} [Field K]
namespace GlobalTheory.FieldModel
namespace HasModel
theorem _root_.solution {X U V W : Over (Sp K)} (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V)
    (hu : IsOpenImmersion u.left) (hv : IsOpenImmersion v.left) (h : IsPullback p.left q.left u.left v.left)
    (hc : ∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left)
    (h₁ : QuasiCompact W.hom) (h₂ : QuasiSeparated W.hom) (h₃ : LocallyOfFiniteType U.hom)
    (h₄ : LocallyOfFiniteType V.hom) (hU : HasModel U) (hV : HasModel V) (hW : HasModel W) : HasModel X := by
  classical
  obtain ⟨sU, hU⟩ := hU
  obtain ⟨sV, hV⟩ := hV
  obtain ⟨sW, hW⟩ := hW
  let k₀ := Subfield.closure ((sU ∪ sV ∪ sW : Finset K) : Set K)
  have sub : ∀ t : Finset K, t ⊆ sU ∪ sV ∪ sW → (t : Set K) ⊆ Set.range k₀.subtype := fun t ht x hx =>
    ⟨⟨x, Subfield.subset_closure (ht hx)⟩, rfl⟩
  obtain ⟨U₀, φU, HU⟩ := hU k₀ k₀.subtype (sub _ (by intro x; simp; tauto))
  obtain ⟨V₀, φV, HV⟩ := hV k₀ k₀.subtype (sub _ (by intro x; simp; tauto))
  obtain ⟨W₀, φW, HW⟩ := hW k₀ k₀.subtype (sub _ (by intro x; simp; tauto))
  obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K k₀.subtype W U W₀ U₀ φW φU HW HU h₁ h₂ h₃ p
  obtain ⟨s₂, hs₂⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K k₀.subtype W V W₀ V₀ φW φV HW HV h₁ h₂ h₄ q
  refine ⟨sU ∪ sV ∪ sW ∪ (s₁ ∪ s₂), fun k _ β hβ => ?_⟩
  rw [Finset.coe_union, Finset.coe_union s₁, Set.union_subset_iff, Set.union_subset_iff] at hβ
  obtain ⟨α, hα⟩ := exists_factor β _ hβ.1
  obtain ⟨ψU, eU, PU⟩ := exists_baseChange (spMap_comp hα) HU
  obtain ⟨ψV, eV, PV⟩ := exists_baseChange (spMap_comp hα) HV
  obtain ⟨ψW, eW, PW⟩ := exists_baseChange (spMap_comp hα) HW
  obtain ⟨p₁, hp⟩ := hs₁ k α β hα hβ.2.1 _ _ ψW _ ψU _ (.of_hasPullback _ _) (.of_hasPullback _ _) eW eU PW.w PU.w
  obtain ⟨q₁, hq⟩ := hs₂ k α β hα hβ.2.2 _ _ ψW _ ψV _ (.of_hasPullback _ _) (.of_hasPullback _ _) eW eV PW.w PV.w
  exact GlobalTheory.T.glue_models_over_subfield k K β X U V W u v p q hu hv h hc _ _ _ ψU ψV ψW PU PV PW p₁ q₁ hp hq
end HasModel
end GlobalTheory.FieldModel
