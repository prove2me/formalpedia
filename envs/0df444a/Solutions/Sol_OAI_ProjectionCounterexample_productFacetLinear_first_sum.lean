-- Prove2me | solution 1 for OAI.ProjectionCounterexample.productFacetLinear_first_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:24:15.9619+00:00
-- url     : https://prove2.me/submissions/bbdbb81b-5bb3-4bc6-b368-9ce9d7e4160f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean:L103-L124
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.productFacetLinear_first_sum. The node keeps its source
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

lemma first_succAbove_first (i : Fin 10) (j : Fin 9) :
    (i.castAdd 10).succAbove (j.castAdd 10) = (i.succAbove j).castAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd]
  split_ifs <;> rfl

lemma first_succAbove_second (i : Fin 10) (j : Fin 10) :
    (i.castAdd 10).succAbove (j.natAdd 9) = j.natAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs with h
  · omega
  · simp only [Fin.val_succ, Fin.val_natAdd]
    omega

end ProjectionCounterexample

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductFacetGraphs ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

lemma firstBlock_productFacetLinear_first (i : Option (Fin 10)) (x : E 19) :
    firstBlock (productFacetLinear (false, i) x) =
      simplexFacetLinear 9 i ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).1 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) x)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

lemma secondBlock_productFacetLinear_first (i : Option (Fin 10)) (x : E 19) :
    secondBlock (productFacetLinear (false, i) x) =
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).2 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) x)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

lemma inner_firstSumGraph (x : E 19) :
    ⟪firstSumGraph, x⟫ = ⟪allOnes 9, ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).1⟫ := by
  rw [DiagonalZonotope.inner_finAdd 9 10]
  have h : (@EuclideanSpace.finAddEquivProd ℝ _ 9 10) firstSumGraph =
      (allOnes 9, 0) := (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).apply_symm_apply _
  rw [h]
  simp only [inner_zero_left, add_zero]

lemma productFacetLinear_first_sum :
    productFacetLinear (false, none) = graphLinear ((Fin.last 9).castAdd 10) firstSumGraph := by
  ext x j
  induction j using ((Fin.last 9).castAdd 10).succAboveCases
  · rw [graphLinear_same, inner_firstSumGraph]
    change firstBlock (productFacetLinear (false, none) x) (Fin.last 9) = _
    rw [firstBlock_productFacetLinear_first]
    simp [simplexFacetLinear]
  · rename_i j
    rw [graphLinear_succAbove]
    induction j using Fin.addCases (m := 9) (n := 10) with
    | left j =>
      rw [first_succAbove_first]
      change firstBlock (productFacetLinear (false, none) x) ((Fin.last 9).succAbove j) = _
      rw [firstBlock_productFacetLinear_first]
      simp only [simplexFacetLinear, graphLinear_succAbove]
      rfl
    | right j =>
      rw [first_succAbove_second]
      change secondBlock (productFacetLinear (false, none) x) j = _
      rw [secondBlock_productFacetLinear_first]
      rfl

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem solution :
    productFacetLinear (false, none) = graphLinear ((Fin.last 9).castAdd 10) firstSumGraph := by
  first
    | exact OAI.ProjectionCounterexample.productFacetLinear_first_sum
    | (apply OAI.ProjectionCounterexample.productFacetLinear_first_sum <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.productFacetLinear_first_sum <;> assumption)
