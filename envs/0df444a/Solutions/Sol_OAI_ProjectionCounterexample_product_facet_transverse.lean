-- Prove2me | solution 1 for OAI.ProjectionCounterexample.product_facet_transverse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:21:25.328401+00:00
-- url     : https://prove2.me/submissions/a0578e8a-8106-4643-b4ce-129a38cf5e5e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetCharts.lean:L149-L181
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.product_facet_transverse. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_facet_transverse

-- ---- from OAI.Geometry.ProjectionBody.ProductFacetCharts ----
namespace OAI

/-! Explicit nineteen-dimensional affine charts on the twenty-two product facets. -/
noncomputable section
open Set

namespace ProjectionCounterexample

private lemma simplexFunctional_ten_ne_zero (j : Option (Fin 10)) :
    simplexFunctional 10 j ≠ 0 := by
  intro heq
  cases j with
  | none =>
    have h := LinearMap.congr_fun heq (EuclideanSpace.single (0 : Fin 10) 1)
    simp at h
  | some j =>
    have h := LinearMap.congr_fun heq (EuclideanSpace.single j 1)
    simp at h

/-- Every other defining hyperplane cuts a product facet chart transversely. -/
theorem product_facet_transverse (i j : Bool × Option (Fin 10)) (hij : i ≠ j) :
    (productFunctional j).comp (productFacetLinear i) ≠ 0 := by
  rcases i with ⟨bi, i⟩
  rcases j with ⟨bj, j⟩
  intro heq
  cases bi <;> cases bj
  · apply simplex_facet_transverse (n := 9) (by decide) i j
      (fun h => hij (congrArg (fun k => (false, k)) h))
    ext z
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (z, 0))
    simpa only [LinearMap.comp_apply, productFunctional_first,
      productFacetLinear_first_first, LinearMap.zero_apply] using h
  · apply simplexFunctional_ten_ne_zero j
    ext w
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (0, w))
    simpa only [LinearMap.comp_apply, productFunctional_second,
      productFacetLinear_first_second, LinearMap.zero_apply] using h
  · apply simplexFunctional_ten_ne_zero j
    ext z
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (z, 0))
    simpa only [LinearMap.comp_apply, productFunctional_first,
      productFacetLinear_second_first, LinearMap.zero_apply] using h
  · apply simplex_facet_transverse (n := 9) (by decide) i j
      (fun h => hij (congrArg (fun k => (true, k)) h))
    ext w
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (0, w))
    simpa only [LinearMap.comp_apply, productFunctional_second,
      productFacetLinear_second_second, LinearMap.zero_apply] using h

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set

theorem solution (i j : Bool × Option (Fin 10)) (hij : i ≠ j) :
    (productFunctional j).comp (productFacetLinear i) ≠ 0 := by
  first
    | exact OAI.ProjectionCounterexample.product_facet_transverse i j hij
    | exact OAI.ProjectionCounterexample.product_facet_transverse
    | (apply OAI.ProjectionCounterexample.product_facet_transverse <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.product_facet_transverse <;> assumption)
