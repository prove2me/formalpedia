-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_oAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:08:21.279866+00:00
-- url     : https://prove2.me/submissions/1eb3717f-a89d-43a8-9349-f61acb6f2de8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_quasiCompact_and_dominant
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_ExtUnique_existsUnique_oAct_pullback
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
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] {G : Over S} [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) {O : Type} [CommRing O] (i : OAct O ((Over.pullback j).obj G)) :
    ∃! a : OAct O G, OAct.pullback j G a = i := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  refine existsUnique_oAct_pullback j i fun x => ?_
  have := i.hom x
  obtain ⟨F, ⟨-, hF⟩, -⟩ := h.of_isOpenImmersion hS j hG hG (i.act x)
  exact ⟨F, hF⟩
end GlobalTheory.Published.SemiAbelianHomExtension
