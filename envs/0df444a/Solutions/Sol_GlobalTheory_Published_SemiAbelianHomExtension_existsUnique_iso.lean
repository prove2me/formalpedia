-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:22.37968+00:00
-- url     : https://prove2.me/submissions/dee54649-4360-4fde-a8ae-12a0b7f8bcf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_quasiCompact_and_dominant
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_ExtUnique_comp_eq_id_of_pullback
import Theorems.Thm_GlobalTheory_ExtUnique_flat_and_isSeparated_of_isSemiAbelian


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj H)
    [IsMonHom e.hom] : ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isOpenImmersion hS j hG hH e.hom
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := h.of_isOpenImmersion hS j hH hG e.inv
  obtain ⟨h₁, h₂⟩ := comp_eq_id_of_pullback j e F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, ⟨hF, hF'⟩, fun E hE => Iso.ext (hu E.hom hE)⟩
end GlobalTheory.Published.SemiAbelianHomExtension
