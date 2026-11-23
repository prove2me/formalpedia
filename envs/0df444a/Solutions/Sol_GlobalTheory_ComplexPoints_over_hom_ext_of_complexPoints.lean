-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:28.164533+00:00
-- url     : https://prove2.me/submissions/4d6eed2b-5903-45a9-853a-b4423ca69380

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_hom_ext_of_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution {A B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)} [LocallyOfFiniteType A.hom]
    [IsReduced A.left] [IsSeparated B.hom] {f g : A ⟶ B}
    (h : ∀ x : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ A, x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine _root_.GlobalTheory.ComplexPoints.hom_ext_of_points (K := ℂ) A.hom B.hom
    (by rw [Over.w f, Over.w g]) fun x hx => ?_
  have := h (Over.homMk x (by simpa using hx))
  simpa using congrArg (fun k => k.left) this
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
