-- Prove2me | solution 1 for GlobalTheory.FieldModel.exists_finite_torusExtension_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:35:16.524214+00:00
-- url     : https://prove2.me/submissions/2122ae24-cf90-4269-af17-0ad544d320cd

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
import Theorems.Thm_GlobalTheory_FieldModel_hasModel
import Theorems.Thm_GlobalTheory_FieldModel_sq_fst
import Theorems.Thm_GlobalTheory_FieldModel_sq_snd
import Theorems.Thm_GlobalTheory_FieldModel_exists_finite_torusExtension_of_model
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.FieldModel.sq_fst
attribute [reassoc] GlobalTheory.FieldModel.sq_snd

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FieldModel
variable {K : Type} [Field K]
namespace GlobalTheory.FieldModel
theorem _root_.solution {k K : Type} [Field k] [Field K] (σ : k →+* K) (G : Over (Sp k))
    [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsSeparated G.hom]
    (T : TorusExtension ((Over.pullback (spMap σ)).obj G)) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ →
      s ⊆ Set.range β → Nonempty (TorusExtension ((Over.pullback (spMap α)).obj G)) := by
  let _ := T.grpB
  have := T.isAbelian.proper
  obtain ⟨s₀, hs₀⟩ := hasModel T.B
  let k₀ := Subfield.closure ((s₀ : Set K) ∪ Set.range σ)
  let α₀ : k →+* k₀ := σ.codRestrict k₀ fun x => Subfield.subset_closure (Or.inr ⟨x, rfl⟩)
  have e₀ : k₀.subtype.comp α₀ = σ := rfl
  obtain ⟨B₀, φ₀, H₀⟩ := hs₀ k₀ k₀.subtype fun x hx => ⟨⟨x, Subfield.subset_closure (Or.inl hx)⟩, rfl⟩
  obtain ⟨s, hs, h⟩ := exists_finite_torusExtension_of_model e₀ G T H₀
  refine ⟨s₀ ∪ s, s₀.finite_toSet.union hs, fun k₁ _ α β hαβ hb => ?_⟩
  obtain ⟨b₀, b₁⟩ := Set.union_subset_iff.1 hb
  obtain ⟨ρ, hρ⟩ := exists_factor β ((s₀ : Set K) ∪ Set.range σ)
    (Set.union_subset b₀ (by rintro _ ⟨x, rfl⟩; exact ⟨α x, by rw [← hαβ]; rfl⟩))
  exact h k₁ α ρ β hαβ hρ (RingHom.ext fun x => β.injective
    ((congrArg (fun f => f (α₀ x)) hρ).trans (congrArg (fun f => f x) hαβ).symm)) b₁
end GlobalTheory.FieldModel
