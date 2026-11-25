-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:38:10.680508+00:00
-- url     : https://prove2.me/submissions/5e7580a8-71b2-4159-9fef-30b9a96c05af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isGrpPullback
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_left_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f := by
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isGrpPullback hS hG hH (isGrpPullback_pullback G j)
    (isGrpPullback_pullback H j) f
  refine ⟨F, ⟨hF, ?_⟩, fun F' hF' => hu F' ⟨hF'.1, ?_⟩⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback_map_left_fst j F).trans hF'.symm
    · exact (Over.w _).trans (Over.w _).symm
  · rw [← hF'.2]
    exact pullback_map_left_fst j F'
end GlobalTheory.Published.SemiAbelianHomExtension
