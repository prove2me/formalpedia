-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.mapGrp_map_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:12.401368+00:00
-- url     : https://prove2.me/submissions/eeaa74ec-41bd-4fca-b576-22ed3acc5a94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_quasiCompact_and_dominant
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_ExtUnique_flat_and_isSeparated_of_isSemiAbelian
import Theorems.Thm_GlobalTheory_ExtUnique_mapGrp_map_injective


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
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] (G H : Grp (Over S))
    (hG : IsSemiAbelian G.X) (hH : IsSemiAbelian H.X) :
    Function.Bijective ((Over.pullback j).mapGrp.map : (G ⟶ H) → _) := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G.X hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H.X hH
  refine ⟨mapGrp_map_injective j G H, fun f => ?_⟩
  have : IsMonHom (M := (Over.pullback j).obj G.X) (N := (Over.pullback j).obj H.X) f.hom.hom :=
    f.hom.isMonHom_hom
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h.of_isOpenImmersion hS j hG hH f.hom.hom
  refine ⟨Grp.homMk F, ?_⟩
  ext1
  exact hF'
end GlobalTheory.Published.SemiAbelianHomExtension
