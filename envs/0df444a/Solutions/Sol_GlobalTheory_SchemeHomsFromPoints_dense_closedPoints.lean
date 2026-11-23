-- Prove2me | solution 1 for GlobalTheory.SchemeHomsFromPoints.dense_closedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:20.097123+00:00
-- url     : https://prove2.me/submissions/504f42c7-5e5e-4885-82df-d800cb02ac89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints

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
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] :
    Dense (closedPoints X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  rw [dense_iff_closure_eq]
  exact closure_closedPoints
end GlobalTheory.SchemeHomsFromPoints
