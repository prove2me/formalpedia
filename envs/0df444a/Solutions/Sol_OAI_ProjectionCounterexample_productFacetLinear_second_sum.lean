-- Prove2me | solution 1 for OAI.ProjectionCounterexample.productFacetLinear_second_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:25:03.954676+00:00
-- url     : https://prove2.me/submissions/47cd3d5c-267c-4149-9d9a-78748ad3fd85

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean:L126-L147
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.productFacetLinear_second_sum. The node keeps its source
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

-- ---- from OAI.Geometry.Zonotope.Euclidean ----
namespace OAI

/-! Coordinate and Euclidean versions of the explicit centered zonotope. -/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

lemma inner_eq_coordinates (u x : EuclideanSpace ℝ ι) :
    ⟪u, x⟫ = ∑ i, u i * x i := by
  simp only [PiLp.inner_apply, Real.inner_apply]

end DiagonalZonotope

end

end OAI

-- ---- from OAI.Geometry.Zonotope.Product ----
namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace DiagonalZonotope

lemma finAddEquivProd_apply (n m : ℕ) (x : EuclideanSpace ℝ (Fin (n + m))) :
    EuclideanSpace.finAddEquivProd x =
      (WithLp.toLp 2 (fun i : Fin n => x (Fin.castAdd m i)),
       WithLp.toLp 2 (fun i : Fin m => x (Fin.natAdd n i))) := by
  rfl

lemma inner_finAdd (n m : ℕ) (u x : EuclideanSpace ℝ (Fin (n + m))) :
    ⟪u, x⟫ =
      ⟪(EuclideanSpace.finAddEquivProd u).1, (EuclideanSpace.finAddEquivProd x).1⟫ +
      ⟪(EuclideanSpace.finAddEquivProd u).2, (EuclideanSpace.finAddEquivProd x).2⟫ := by
  simp only [inner_eq_coordinates, finAddEquivProd_apply]
  exact Fin.sum_univ_add (fun i => u i * x i)

end DiagonalZonotope

end

end OAI

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

lemma inner_secondSumGraph (x : E 19) :
    ⟪secondSumGraph, x⟫ = ⟪allOnes 9, ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).2⟫ := by
  rw [DiagonalZonotope.inner_finAdd 10 9]
  have h : (@EuclideanSpace.finAddEquivProd ℝ _ 10 9) secondSumGraph =
      (0, allOnes 9) := (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).apply_symm_apply _
  rw [h]
  simp only [inner_zero_left, zero_add]

lemma productFacetLinear_second_sum :
    productFacetLinear (true, none) = graphLinear ((Fin.last 9).natAdd 10) secondSumGraph := by
  ext x j
  induction j using ((Fin.last 9).natAdd 10).succAboveCases
  · rw [graphLinear_same, inner_secondSumGraph]
    change secondBlock (productFacetLinear (true, none) x) (Fin.last 9) = _
    rw [secondBlock_productFacetLinear_second]
    simp [simplexFacetLinear]
  · rename_i j
    rw [graphLinear_succAbove]
    induction j using Fin.addCases (m := 10) (n := 9) with
    | left j =>
      rw [second_succAbove_first]
      change firstBlock (productFacetLinear (true, none) x) j = _
      rw [firstBlock_productFacetLinear_second]
      rfl
    | right j =>
      rw [second_succAbove_second]
      change secondBlock (productFacetLinear (true, none) x) ((Fin.last 9).succAbove j) = _
      rw [secondBlock_productFacetLinear_second]
      simp only [simplexFacetLinear, graphLinear_succAbove]
      rfl

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem solution :
    productFacetLinear (true, none) = graphLinear ((Fin.last 9).natAdd 10) secondSumGraph := by
  first
    | exact OAI.ProjectionCounterexample.productFacetLinear_second_sum
    | (apply OAI.ProjectionCounterexample.productFacetLinear_second_sum <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.productFacetLinear_second_sum <;> assumption)
