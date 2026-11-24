-- Prove2me | solution 1 for GlobalTheory.CoverOpCompat.push_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:31.829839+00:00
-- url     : https://prove2.me/submissions/3adb6fdc-dfcc-4c75-b5df-db9920a13260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPoints
import Theorems.Thm_GlobalTheory_CoverOpCompat_push_mul
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
theorem _root_.solution (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p : Over.mk ρ ⟶ G') (x : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) :
    (x⁻¹).left = (p⁻¹).left ≫ φ := by
  subst e

  have hw : ((p⁻¹).left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have hxz : (x * z).left = (p * p⁻¹).left ≫ φ := push_mul h rfl p p⁻¹ x z hx rfl
  rw [_root_.mul_inv_cancel, ← isGrpPullback_one_left h ρ] at hxz
  have hxz' : x * z = 1 := Over.OverMorphism.ext hxz
  have hz : x⁻¹ = z := (_root_.eq_inv_of_mul_eq_one_right hxz').symm
  rw [hz]
  rfl
end GlobalTheory.CoverOpCompat
