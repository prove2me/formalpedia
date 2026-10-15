-- Prove2me | solution 1 for OAI.ProjectionCounterexample.graphProjection_normDet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:28:25.58653+00:00
-- url     : https://prove2.me/submissions/c0e608bf-f107-4360-b551-e238ede35840

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/GraphProjection.lean:L13-L31
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.graphProjection_normDet. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Theorems.Thm_OAI_ProjectionCounterexample_graphLinear_normDet
import Theorems.Thm_OAI_ProjectionCounterexample_normDet_project_comp

-- ---- from OAI.Geometry.ProjectionBody.GraphChart ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem graphNormal_ne_zero {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    graphNormal i a ≠ 0 := by
  intro h
  have := congrArg (fun x : E (n + 1) => x i) h
  simp at this

theorem graphNormal_inner_graphLinear {n : ℕ} (i : Fin (n + 1)) (a x : E n) :
    ⟪graphNormal i a, graphLinear i a x⟫ = 0 := by
  simp [graphNormal, graphLinear, inner_add_left, inner_sub_right,
    real_inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, (insertZero i).inner_map_map]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.GraphProjection ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- Projection of a graph chart cancels the length of its unnormalized normal. -/
theorem graphProjection_normDet {n : ℕ} (i : Fin (n + 1)) (a : E n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (graphLinear i a)).normDet =
      |⟪graphNormal i a, u⟫| := by
  let w := graphNormal i a
  have hw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr (graphNormal_ne_zero i a)
  let v := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hw]
  have hmem (x : E n) : ⟪v, graphLinear i a x⟫ = 0 := by
    rw [show v = ‖w‖⁻¹ • graphNormal i a from rfl, real_inner_smul_left,
      graphNormal_inner_graphLinear, mul_zero]
  change ((perpendicularTo u).starProjection.toLinearMap.comp (graphLinear i a)).normDet = _
  rw [normDet_project_comp (graphLinear i a) hv hu hmem (by simp),
    graphLinear_normDet]
  change |⟪‖w‖⁻¹ • w, u⟫| * ‖w‖ = |⟪w, u⟫|
  rw [real_inner_smul_left, abs_mul, abs_inv, abs_of_nonneg (norm_nonneg w)]
  field_simp [hw]

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (i : Fin (n + 1)) (a : E n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (graphLinear i a)).normDet =
      |⟪graphNormal i a, u⟫| := by
  first
    | exact OAI.ProjectionCounterexample.graphProjection_normDet i a hu
    | exact OAI.ProjectionCounterexample.graphProjection_normDet
    | (apply OAI.ProjectionCounterexample.graphProjection_normDet <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.graphProjection_normDet <;> assumption)
