-- Prove2me | solution 1 for GlobalTheory.WitnessData.comm_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:05.253225+00:00
-- url     : https://prove2.me/submissions/7b9eebf7-0788-4514-be21-88154be3244f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution {S S₀ : Scheme.{0}} {B B' : Over S} {B₀ : Over S₀} {f : S ⟶ S₀} {i : S ⟶ S} (hi : i = 𝟙 S)
    {φ : B.left ⟶ B₀.left} (hφ : IsPullback φ B.hom B₀.hom f) (e : B' ⟶ (Over.pullback i).obj B)
    {φ' : B'.left ⟶ B₀.left} (hφ' : φ' = (e.left ≫ pullback.fst B.hom i) ≫ φ) {x : B ⟶ B} {x' : B' ⟶ B'}
    {x₀ : B₀.left ⟶ B₀.left} (h : x.left ≫ φ = φ ≫ x₀) (h' : x'.left ≫ φ' = φ' ≫ x₀) :
    x' ≫ e = e ≫ (Over.pullback i).map x := by
  have a : e.left ≫ pullback.snd B.hom i = B'.hom := Over.w e
  have hw : (e.left ≫ pullback.fst B.hom i) ≫ B.hom = B'.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, a, hi, Category.comp_id]
  have e₁ : x'.left ≫ e.left ≫ pullback.fst B.hom i = (e.left ≫ pullback.fst B.hom i) ≫ x.left := by
    apply hφ.hom_ext
    · rw [Category.assoc, ← hφ', h', Category.assoc, h, ← Category.assoc, ← hφ']
    · rw [Category.assoc, hw, Over.w, Category.assoc, Over.w, hw]
  have e₂ : ((Over.pullback i).map x).left ≫ pullback.fst B.hom i = pullback.fst _ _ ≫ x.left :=
    pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · show (x'.left ≫ e.left) ≫ _ = (e.left ≫ ((Over.pullback i).map x).left) ≫ _
    rw [Category.assoc, Category.assoc, e₂, ← Category.assoc e.left]
    exact e₁
  · exact (Over.w (x' ≫ e)).trans (Over.w (e ≫ (Over.pullback i).map x)).symm
end GlobalTheory.WitnessData
