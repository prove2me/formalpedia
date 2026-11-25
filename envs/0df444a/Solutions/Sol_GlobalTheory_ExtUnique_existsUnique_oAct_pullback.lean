-- Prove2me | solution 1 for GlobalTheory.ExtUnique.existsUnique_oAct_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:49:02.466869+00:00
-- url     : https://prove2.me/submissions/e6e9f36b-0ed3-49d3-b47c-2539ca04afbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_left_fst
import Theorems.Thm_GlobalTheory_ExtUnique_oAct_ext
import Theorems.Thm_GlobalTheory_ExtUnique_existsUnique_oAct_of_isGrpPullback
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
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
variable (j)
namespace GlobalTheory.ExtUnique
theorem _root_.solution {O : Type} [CommRing O] {G : Over S} [GrpObj G] [IsCommMonObj G] [Flat G.hom]
    [IsSeparated G.hom] (i : OAct O ((Over.pullback j).obj G))
    (hi : ∀ x, ∃ f : G ⟶ G, (Over.pullback j).map f = i.act x) :
    ∃! a : OAct O G, OAct.pullback j G a = i := by
  obtain ⟨a, ha, hu⟩ := existsUnique_oAct_of_isGrpPullback (isGrpPullback_pullback G j) i fun x => by
    obtain ⟨f, hf⟩ := hi x
    exact ⟨f, by rw [← hf, pullback_map_left_fst]⟩
  refine ⟨a, oAct_ext fun x => ?_, fun b hb => hu b fun x => ?_⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback_map_left_fst j _).trans (ha x).symm
    · exact (Over.w _).trans (Over.w _).symm
  · rw [← hb]
    exact pullback_map_left_fst j _
end GlobalTheory.ExtUnique
