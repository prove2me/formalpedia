-- Prove2me | solution 1 for OAI.DiagonalZonotope.centered_support_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:10:48.103773+00:00
-- url     : https://prove2.me/submissions/1edbcee7-7509-4d51-84db-ca353dfffd93

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Support.lean:L67-L82
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalZonotope.centered_support_le. The node keeps its source
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

-- ---- from OAI.Geometry.Zonotope.Support ----
namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

lemma interval_mul_bound (a r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    2 * (a * r) ≤ |a| + a := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    linarith [mul_le_mul_of_nonneg_left hr1 ha]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge ha)) hr0]

/-- Every point satisfies the exact support bound, expressed as a coordinate pairing. -/
theorem centered_support_le (u x : ι → ℝ) (hx : x ∈ centered) :
    (∑ i, u i * x i) ≤ ((∑ i, |u i|) + |∑ i, u i|) / 2 := by
  rcases hx with ⟨q, hq, t, ht, hx⟩
  have heq (i : ι) : x i = q i + t - 1 := by
    have h : x i + 1 = q i + t := by simpa using congrFun hx i
    linarith
  have hqbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    interval_mul_bound (u i) (q i) (hq i).1 (hq i).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hqbound
  have htbound := interval_mul_bound (∑ i, u i) t ht.1 ht.2
  have hdot : (∑ i, u i * x i) =
      (∑ i, u i * q i) + (∑ i, u i) * t - ∑ i, u i := by
    simp only [heq, mul_sub, mul_add, mul_one, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_mul]
  linarith

end DiagonalZonotope

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalZonotope
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem solution (u x : ι → ℝ) (hx : x ∈ centered) :
    (∑ i, u i * x i) ≤ ((∑ i, |u i|) + |∑ i, u i|) / 2 := by
  first
    | exact OAI.DiagonalZonotope.centered_support_le u x hx
    | exact OAI.DiagonalZonotope.centered_support_le
    | (apply OAI.DiagonalZonotope.centered_support_le <;> assumption)
    | (intros; apply OAI.DiagonalZonotope.centered_support_le <;> assumption)
