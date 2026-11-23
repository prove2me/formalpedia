-- Prove2me | solution 1 for GlobalTheory.finite_of_finite_sections
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:28.35686+00:00
-- url     : https://prove2.me/submissions/d0017bdd-7679-49b9-ba6c-f02d87808071

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P : Scheme.{0}}
    (s : P ⟶ Spec (.of Ω)) [LocallyOfFiniteType s]
    (h : Finite {x : Spec (.of Ω) ⟶ P // x ≫ s = 𝟙 _}) : Finite P := by
  have hJ : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  have hc : (closedPoints P).Finite := by
    have : Finite (closedPoints P) := Finite.of_equiv _ (pointEquivClosedPoint s)
    exact Set.toFinite _
  have hcl : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact hc.isClosed_biUnion fun x hx ↦ hx
  have hu : closedPoints P = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints (X := P) isClosed_univ
    rwa [Set.univ_inter, hcl.closure_eq] at this
  exact Set.finite_univ_iff.mp (hu ▸ hc)
end GlobalTheory
