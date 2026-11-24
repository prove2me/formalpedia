-- Prove2me | solution 1 for GlobalTheory.ConstEndo.unit_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:22.209608+00:00
-- url     : https://prove2.me/submissions/61d771d4-7f3e-433b-9b2b-ca6a62ae703c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubsingletonSpDualNumber
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EndoConstantFamilyDualNumbersEqBaseChange

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.ConstEndo
namespace GlobalTheory.ConstEndo
theorem _root_.solution {S S₀ : Scheme.{0}} {f : S ⟶ S₀} {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀]
    {φ : X.left ⟶ X₀.left} (h : IsGrpPullback X X₀ f φ) :
    (η[X]).left ≫ φ = f ≫ (η[X₀]).left := by
  obtain ⟨hpb, hmul⟩ := h

  have hw : ((η[X]).left ≫ φ) ≫ X₀.hom = (𝟙_ (Over S)).hom ≫ f := by
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w]
  let x₀ : Over.mk ((𝟙_ (Over S)).hom ≫ f) ⟶ X₀ := Over.homMk ((η[X]).left ≫ φ) hw

  have hηη : (η[X] : 𝟙_ (Over S) ⟶ X) * η[X] = η[X] := by
    rw [MonObj.one_eq_one, _root_.one_mul]
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hmul (𝟙_ (Over S)) η[X] η[X] x₀ x₀ rfl rfl, hηη]
    rfl
  have h1 : x₀ = 1 := by
    simpa using hx
  have h2 := congrArg CommaMorphism.left h1
  simp only [x₀, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom,
    Over.tensorUnit_hom] at h2
  exact h2
end GlobalTheory.ConstEndo
