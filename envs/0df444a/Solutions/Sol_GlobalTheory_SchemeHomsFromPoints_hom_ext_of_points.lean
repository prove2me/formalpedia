-- Prove2me | solution 1 for GlobalTheory.SchemeHomsFromPoints.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:59.475477+00:00
-- url     : https://prove2.me/submissions/2f347895-162a-4ebe-8cf0-21e1d475f6de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_dense_closedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    [Y.IsSeparated] (f g : X ⟶ Y) (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g (terminal.from Y) (closedPoints X)
    (dense_closedPoints p) ?_ (terminal.hom_ext _ _)
  intro x hx
  have h := H (pointOfClosedPoint p x hx) (pointOfClosedPoint_comp p x hx)
  rw [← cancel_epi (Spec.map (residueFieldIsoBase p x hx).hom)]
  simpa only [pointOfClosedPoint, Category.assoc] using h
end GlobalTheory.SchemeHomsFromPoints
