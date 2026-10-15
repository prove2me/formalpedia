-- Prove2me | solution 1 for OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:35:02.958851+00:00
-- url     : https://prove2.me/submissions/3b8ebe79-71fb-4239-aa81-4c2a5ac02c7c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/Arithmetic.lean:L13-L30
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume

-- ---- from OAI.Geometry.ProjectionBody.Arithmetic ----
namespace OAI

/-! Numerical consequences, to be used only after the geometric volume identities. -/

namespace ProjectionCounterexample

/-- Algebraic double-counting identity used after the visible-face measure sum.
The balance condition is later proved from the actual simplex facet vectors. -/
theorem sum_positive_eq_half_sum_abs {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    (∑ i with 0 < a i, a i) = (∑ i, |a i|) / 2 := by
  classical
  have hi (i : ι) : 2 * (if 0 < a i then a i else 0) = |a i| + a i := by
    split_ifs with h
    · rw [abs_of_pos h]
      linarith
    · rw [abs_of_nonpos (le_of_not_gt h)]
      linarith
  have hs : 2 * (∑ i, if 0 < a i then a i else 0) = ∑ i, |a i| := by
    rw [Finset.mul_sum]
    simp_rw [hi]
    rw [Finset.sum_add_distrib, ha, add_zero]
  rw [Finset.sum_filter]
  linarith

end ProjectionCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample

theorem solution {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    (∑ i with 0 < a i, a i) = (∑ i, |a i|) / 2 := by
  first
    | exact OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs a ha
    | exact OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs
    | (apply OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.sum_positive_eq_half_sum_abs <;> assumption)
