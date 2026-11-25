-- Prove2me | solution 1 for GlobalTheory.FieldModel.hasModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:01.56296+00:00
-- url     : https://prove2.me/submissions/4061549f-718c-4c6c-af4a-71021e804225

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
import Theorems.Thm_GlobalTheory_FieldModel_HasModel_sup
import Theorems.Thm_P2M_GlobalTheory_T_exists_finset_model_of_isAffine__8386d6febae7


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
theorem _root_.solution (X : Over (Sp K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    HasModel X := by
  have sep : IsSeparated (terminal.from X.left) := by
    rw [← terminal.comp_from X.hom]; infer_instance
  have : X.left.IsSeparated := ⟨sep⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have aff : ∀ V : X.left.Opens, IsAffineOpen V → HasModel (part X V) := fun V hV =>
    GlobalTheory.T.exists_finset_model_of_isAffine' K (part X V) hV (inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X.hom)))
  have cpt : ∀ S V : X.left.Opens, IsCompact S.carrier → IsAffineOpen V →
      IsCompact ((S ⊓ V : X.left.Opens) : Set X.left) := fun S V hS hV =>
    QuasiSeparatedSpace.inter_isCompact _ _ S.isOpen hS V.isOpen hV.isCompact
  have h₁ : ∀ S : X.left.Opens, IsCompact (S : Set X.left) → ∀ V, IsAffineOpen V → HasModel (part X (S ⊓ V)) := by
    intro S hS
    refine compact_open_induction_on (P := fun S => ∀ V, IsAffineOpen V → HasModel (part X (S ⊓ V))) S hS ?_ ?_
    · intro V _
      rw [bot_inf_eq]
      exact aff _ (isAffineOpen_bot _)
    · intro S hS U ih V hV
      have hUV : IsAffineOpen (U.1 ⊓ V) := U.2.inf hV
      have e : S ⊓ V ⊓ (U.1 ⊓ V) = S ⊓ (U.1 ⊓ V) := by
        rw [inf_assoc, inf_left_comm V, inf_idem]
      rw [inf_sup_right]
      refine HasModel.sup X _ _ ?_ (ih V hV) (aff _ hUV) ?_
      · rw [e]; exact cpt _ _ hS hUV
      · rw [e]; exact ih _ hUV
  have h₂ : HasModel (part X ⊤) := by
    refine compact_open_induction_on (P := fun S => HasModel (part X S)) ⊤ isCompact_univ
      (aff _ (isAffineOpen_bot _)) fun S hS U ih => ?_
    exact HasModel.sup X _ _ (cpt _ _ hS U.2) ih (aff _ U.2) (h₁ S hS _ U.2)
  obtain ⟨s, hs⟩ := h₂
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨X₀, φ, H⟩ := hs k β hβ
  refine ⟨X₀, X.left.topIso.inv ≫ φ, ?_⟩
  have H' : IsPullback X.left.topIso.inv X.hom (part X ⊤).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using H'.paste_horiz H
end GlobalTheory.FieldModel
