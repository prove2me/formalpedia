-- Prove2me | solution 1 for GlobalTheory.CoverOpCompat.push_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:32.517743+00:00
-- url     : https://prove2.me/submissions/605d7910-d324-44ba-bf0b-76bbad27e526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.CoverOpCompat
section
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
private lemma isGrpPullback_one_left (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (ρ : T ⟶ S') :
    (1 : Over.mk (ρ ≫ f) ⟶ G).left = (1 : Over.mk ρ ⟶ G').left ≫ φ := by

  have hw : ((1 : Over.mk ρ ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have huu : (u * u).left = ((1 : Over.mk ρ ⟶ G') * 1).left ≫ φ := h.2 (Over.mk ρ) 1 1 u u rfl rfl
  rw [_root_.mul_one] at huu
  have hsq : u * u = u := Over.OverMorphism.ext huu
  have hu : u = 1 := by
    calc u = u * u * u⁻¹ := (_root_.mul_inv_cancel_right u u).symm
      _ = 1 := by rw [hsq, _root_.mul_inv_cancel]
  rw [← hu]
  rfl
end
end GlobalTheory.CoverOpCompat
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverOpCompat
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
namespace GlobalTheory.CoverOpCompat
theorem _root_.solution (h : IsGrpPullback G' G f φ) :
    f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Out.baseOver S' ⟶ G').left ≫ φ := by

  let c : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
    Over.homMk f (by simp [Out.baseOver])
  have hc : c ≫ (1 : Out.baseOver S ⟶ G) = 1 := MonObj.comp_one c
  have hl : f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ G).left := by
    rw [← hc]
    rfl
  rw [hl]
  exact isGrpPullback_one_left h (Out.baseOver S').hom
end GlobalTheory.CoverOpCompat
