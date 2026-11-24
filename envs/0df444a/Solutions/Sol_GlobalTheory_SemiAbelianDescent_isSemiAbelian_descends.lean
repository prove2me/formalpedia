-- Prove2me | solution 1 for GlobalTheory.SemiAbelianDescent.isSemiAbelian_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:10.741601+00:00
-- url     : https://prove2.me/submissions/771f3db3-d509-4e84-89e5-628c3d17c805

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeometricallyConnectedOfIsPullback
import Theorems.Thm_GlobalTheory_SemiAbelianDescent_exists_lift
import Theorems.Thm_GlobalTheory_SemiAbelianDescent_isSeparated_of_comp
import Theorems.Thm_GlobalTheory_SemiAbelianDescent_quasiCompact_of_comp
import Theorems.Thm_GlobalTheory_SemiAbelianDescent_geometricallyConnected_of_isPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.SemiAbelianDescent
namespace GlobalTheory.SemiAbelianDescent
theorem _root_.solution {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨hc, hsm, hsep, hqc, hgc, hfib⟩ := hG
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hφi : IsIntegralHom φ := MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hsep' : IsSeparated G'.hom := by
    have : IsSeparated (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact isSeparated_of_comp φ G'.hom
  have hqc' : QuasiCompact G'.hom := by
    have : QuasiCompact (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact quasiCompact_of_comp φ G'.hom
  have hgc' : GeometricallyConnected G'.hom := geometricallyConnected_of_isPullback hpb
  refine ⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩
  intro Ω _ _ p
  obtain ⟨q, hq⟩ := exists_lift π p
  obtain ⟨T⟩ := hfib Ω q
  have h1 := isGrpPullback_pullback G q
  have h2 := IsGrpPullback.comp h1 h
  have h3 := isGrpPullback_pullback G' p
  obtain ⟨e, he, -⟩ := grpPullback_iso (h2.congr hq rfl) h3
  exact ⟨torusExtOfIso e T⟩
end GlobalTheory.SemiAbelianDescent
