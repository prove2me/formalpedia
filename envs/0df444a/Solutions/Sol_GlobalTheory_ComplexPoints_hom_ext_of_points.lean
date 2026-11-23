-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:07.784697+00:00
-- url     : https://prove2.me/submissions/f03363cf-6793-449b-a98e-738fce1f5422

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed

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
variable {K : Type u} [Field K] [IsAlgClosed K]
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {K : Type u} [Field K] [IsAlgClosed K]
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution {X Y S : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [LocallyOfFiniteType p]
    [IsReduced X] (q : Y ⟶ S) [IsSeparated q] {f g : X ⟶ Y} (hfg : f ≫ q = g ≫ q)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine ext_of_fromSpecResidueField_eq f g q (closedPoints X)
    (dense_iff_closure_eq.mpr closure_closedPoints) ?_ hfg
  intro y hy
  have e := h (pointOfClosedPoint p y hy) (pointOfClosedPoint_comp p y hy)
  unfold pointOfClosedPoint at e
  simp only [Category.assoc] at e
  exact (cancel_epi _).mp e
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
