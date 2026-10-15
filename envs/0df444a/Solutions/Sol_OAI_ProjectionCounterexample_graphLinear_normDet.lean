-- Prove2me | solution 1 for OAI.ProjectionCounterexample.graphLinear_normDet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:25:54.489671+00:00
-- url     : https://prove2.me/submissions/9e672bec-8458-4660-bb91-8372d615938a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/GraphJacobian.lean:L12-L34
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.graphLinear_normDet. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.GraphChart ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem graphLinear_inner {n : ℕ} (i : Fin (n + 1)) (a x y : E n) :
    ⟪graphLinear i a x, graphLinear i a y⟫ = ⟪x, y⟫ + ⟪a, x⟫ * ⟪a, y⟫ := by
  simp [graphLinear, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, (insertZero i).inner_map_map, mul_comm]

theorem graphNormal_norm_sq {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    ‖graphNormal i a‖ ^ 2 = 1 + ‖a‖ ^ 2 := by
  calc
    ‖graphNormal i a‖ ^ 2 = ⟪graphNormal i a, graphNormal i a⟫ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = 1 + ‖a‖ ^ 2 := by
      unfold graphNormal
      rw [inner_add_left, inner_add_right, inner_add_right]
      simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
        add_comm]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.GraphJacobian ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- The Jacobian of a graph chart is the length of its unnormalized normal. -/
theorem graphLinear_normDet {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    (graphLinear i a).normDet = ‖graphNormal i a‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hGram : Matrix.gram ℝ (fun j => graphLinear i a (b j)) =
      1 + Matrix.replicateCol Unit (fun j => a j) *
        Matrix.replicateRow Unit (fun j => a j) := by
    ext j k
    rw [Matrix.gram_apply, graphLinear_inner]
    simp [b, EuclideanSpace.basisFun_apply, eq_comm,
      EuclideanSpace.inner_single_right, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
  have hsquare : (graphLinear i a).normDet ^ 2 = ‖graphNormal i a‖ ^ 2 := by
    calc
      (graphLinear i a).normDet ^ 2 =
          (Matrix.gram ℝ (fun j => graphLinear i a (b j))).det :=
        (graphLinear i a).normDet_sq_eq_det_gram b
      _ = ‖graphNormal i a‖ ^ 2 := by
        rw [hGram, Matrix.det_one_add_replicateCol_mul_replicateRow,
          graphNormal_norm_sq, EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, pow_two]
  exact (sq_eq_sq₀ (graphLinear i a).normDet_nonneg (norm_nonneg _)).mp hsquare

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    (graphLinear i a).normDet = ‖graphNormal i a‖ := by
  first
    | exact OAI.ProjectionCounterexample.graphLinear_normDet i a
    | exact OAI.ProjectionCounterexample.graphLinear_normDet
    | (apply OAI.ProjectionCounterexample.graphLinear_normDet <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.graphLinear_normDet <;> assumption)
