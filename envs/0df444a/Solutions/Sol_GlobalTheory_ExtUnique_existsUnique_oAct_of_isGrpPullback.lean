-- Prove2me | solution 1 for GlobalTheory.ExtUnique.existsUnique_oAct_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:40.398595+00:00
-- url     : https://prove2.me/submissions/72c8d7f0-e95f-4b2e-8635-f0bb9b17325a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback
import Theorems.Thm_GlobalTheory_ExtUnique_isMonHom_of_isGrpPullback
import Theorems.Thm_GlobalTheory_ExtUnique_oAct_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
namespace GlobalTheory.ExtUnique
theorem _root_.solution {O : Type} [CommRing O] {G : Over S} [GrpObj G] [Flat G.hom]
    [IsSeparated G.hom] {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G j φ)
    (i : OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose f hf using hi
  refine ⟨⟨f, fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩, hf, fun b hb => oAct_ext fun x => ?_⟩
  · have := i.hom x
    exact isMonHom_of_isGrpPullback hG hG (i.act x) (f x) (hf x)
  · refine over_hom_ext_of_isPullback hG.1 ?_
    rw [← hf, i.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine over_hom_ext_of_isPullback hG.1 ?_
    rw [← hf, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine over_hom_ext_of_isPullback hG.1 ?_
    let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hG.1.w
    have h := hG.2 G' (i.act x) (i.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, i.add, ← h]
    rfl
  · exact over_hom_ext_of_isPullback hG.1 ((hb x).symm.trans (hf x))
end GlobalTheory.ExtUnique
