-- Prove2me | solution 1 for OAI.ProjectionCounterexample.productFacetLinear_second_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:23:21.021031+00:00
-- url     : https://prove2.me/submissions/3c52e8e2-bbd8-49d5-bade-8baf9b38ea31

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean:L58-L79
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.productFacetLinear_second_coordinate. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.ProductFacetIndices ----
namespace OAI

namespace ProjectionCounterexample

lemma second_succAbove_first (i : Fin 10) (j : Fin 10) :
    (i.natAdd 10).succAbove (j.castAdd 9) = j.castAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs with h
  · rfl
  · omega

lemma second_succAbove_second (i : Fin 10) (j : Fin 9) :
    (i.natAdd 10).succAbove (j.natAdd 10) = (i.succAbove j).natAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_natAdd]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.val_natAdd] <;> omega

end ProjectionCounterexample

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductFacetGraphs ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

lemma firstBlock_productFacetLinear_second (i : Option (Fin 10)) (x : E 19) :
    firstBlock (productFacetLinear (true, i) x) =
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).1 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) x)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

lemma secondBlock_productFacetLinear_second (i : Option (Fin 10)) (x : E 19) :
    secondBlock (productFacetLinear (true, i) x) =
      simplexFacetLinear 9 i ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).2 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) x)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

lemma productFacetLinear_second_coordinate (i : Fin 10) :
    productFacetLinear (true, some i) = (insertZero (i.natAdd 10)).toLinearMap := by
  ext x j
  induction j using (i.natAdd 10).succAboveCases
  · change secondBlock (productFacetLinear (true, some i) x) i = _
    rw [secondBlock_productFacetLinear_second]
    simp [simplexFacetLinear]
  · rename_i j
    simp only [LinearIsometry.coe_toLinearMap]
    rw [insertZero_succAbove]
    induction j using Fin.addCases (m := 10) (n := 9) with
    | left j =>
      rw [second_succAbove_first]
      change firstBlock (productFacetLinear (true, some i) x) j = _
      rw [firstBlock_productFacetLinear_second]
      rfl
    | right j =>
      rw [second_succAbove_second]
      change secondBlock (productFacetLinear (true, some i) x) (i.succAbove j) = _
      rw [secondBlock_productFacetLinear_second]
      simp only [simplexFacetLinear, LinearIsometry.coe_toLinearMap, insertZero_succAbove]
      rfl

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem solution (i : Fin 10) :
    productFacetLinear (true, some i) = (insertZero (i.natAdd 10)).toLinearMap := by
  first
    | exact OAI.ProjectionCounterexample.productFacetLinear_second_coordinate i
    | exact OAI.ProjectionCounterexample.productFacetLinear_second_coordinate
    | (apply OAI.ProjectionCounterexample.productFacetLinear_second_coordinate <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.productFacetLinear_second_coordinate <;> assumption)
