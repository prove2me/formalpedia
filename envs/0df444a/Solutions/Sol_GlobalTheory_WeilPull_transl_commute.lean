-- Prove2me | solution 1 for GlobalTheory.WeilPull.transl_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:50.543828+00:00
-- url     : https://prove2.me/submissions/92b1594c-2c7d-45ce-8101-c363908e28f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPull
open GlobalTheory.CommPairing
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilPull
theorem _root_.solution {x y : T ⟶ A} (h : x * y = y * x) :
    (translT A x).left ≫ (translPt A y).left = (translT A y).left ≫ (translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc,
    lift_fst, lift_fst]
  show (fst T A ≫ y) * ((fst T A ≫ x) * snd T A) = (fst T A ≫ x) * ((fst T A ≫ y) * snd T A)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← MonObj.comp_mul, ← MonObj.comp_mul, h]
end GlobalTheory.WeilPull
