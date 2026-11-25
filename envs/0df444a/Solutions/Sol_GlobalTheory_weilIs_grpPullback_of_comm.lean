-- Prove2me | solution 1 for GlobalTheory.weilIs_grpPullback_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:27:14.786587+00:00
-- url     : https://prove2.me/submissions/5259ea2d-1bfe-4037-8fd9-363b39358885

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_GlobalTheory_weilIs_grpPullback_of_commute

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
open GlobalTheory
open WeilPull
namespace GlobalTheory
theorem _root_.solution : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    [IsCommMonObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro S S' G G' _ _ _ f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey
  refine weilIs_grpPullback_of_commute S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ?_ ex ey
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · rw [← hp.2 T x y x₀ y₀ ex ey, ← hp.2 T y x y₀ x₀ ey ex, mul_comm x₀ y₀]
  · rw [Over.w, Over.w]
end GlobalTheory
