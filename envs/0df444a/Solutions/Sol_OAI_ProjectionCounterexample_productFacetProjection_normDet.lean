-- Prove2me | solution 1 for OAI.ProjectionCounterexample.productFacetProjection_normDet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:29:21.628324+00:00
-- url     : https://prove2.me/submissions/e4b1e144-a70e-44b9-a487-e5835369ec25

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetProjection.lean:L11-L33
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.productFacetProjection_normDet. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_graphProjection_normDet
import Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_first_coordinate
import Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_first_sum
import Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_second_coordinate
import Theorems.Thm_OAI_ProjectionCounterexample_productFacetLinear_second_sum

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

lemma graphNormal_succAbove {n : ℕ} (i : Fin (n + 1)) (a : E n) (j : Fin n) :
    graphNormal i a (i.succAbove j) = a j := by
  simp [graphNormal]

lemma firstSumGraph_normal :
    graphNormal ((Fin.last 9).castAdd 10) firstSumGraph =
      (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (allOnes 10, 0) := by
  ext j
  induction j using ((Fin.last 9).castAdd 10).succAboveCases
  · rw [graphNormal_same, blockJoin_first]
    rfl
  · rename_i j
    rw [graphNormal_succAbove]
    induction j using Fin.addCases (m := 9) (n := 10) with
    | left j =>
      rw [first_succAbove_first (Fin.last 9) j, firstSumGraph, blockJoin_first, blockJoin_first]
      rfl
    | right j =>
      rw [first_succAbove_second (Fin.last 9) j, firstSumGraph, blockJoin_second, blockJoin_second]

lemma secondSumGraph_normal :
    graphNormal ((Fin.last 9).natAdd 10) secondSumGraph =
      (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (0, allOnes 10) := by
  ext j
  induction j using ((Fin.last 9).natAdd 10).succAboveCases
  · rw [graphNormal_same, blockJoin_second]
    rfl
  · rename_i j
    rw [graphNormal_succAbove]
    induction j using Fin.addCases (m := 10) (n := 9) with
    | left j =>
      rw [second_succAbove_first (Fin.last 9) j, secondSumGraph, blockJoin_first, blockJoin_first]
    | right j =>
      rw [second_succAbove_second (Fin.last 9) j, secondSumGraph, blockJoin_second, blockJoin_second]
      rfl

lemma firstSumGraph_normal_inner (u : E 20) :
    ⟪graphNormal ((Fin.last 9).castAdd 10) firstSumGraph, u⟫ =
      simplexFunctional 10 none (firstBlock u) := by
  rw [firstSumGraph_normal, DiagonalZonotope.inner_finAdd 10 10,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [inner_zero_left, add_zero, inner_allOnes, firstBlock_finAdd, simplexFunctional_none]

lemma secondSumGraph_normal_inner (u : E 20) :
    ⟪graphNormal ((Fin.last 9).natAdd 10) secondSumGraph, u⟫ =
      simplexFunctional 10 none (secondBlock u) := by
  rw [secondSumGraph_normal, DiagonalZonotope.inner_finAdd 10 10,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [inner_zero_left, zero_add, inner_allOnes, secondBlock_finAdd, simplexFunctional_none]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.GraphProjection ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem coordinateProjection_normDet {n : ℕ} (i : Fin (n + 1))
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (insertZero i).toLinearMap).normDet = |u i| := by
  have hL : graphLinear i 0 = (insertZero i).toLinearMap := by
    ext x j
    simp [graphLinear]
  have h := graphProjection_normDet i 0 hu
  simpa [hL, graphNormal, EuclideanSpace.inner_single_left] using h

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductFacetProjection ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- The true projected area scale of each product facet chart. -/
theorem productFacetProjection_normDet (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (productFacetLinear i)).normDet =
      |productFunctional i u| := by
  rcases i with ⟨b, i⟩
  cases b
  · cases i with
    | none =>
      rw [productFacetLinear_first_sum, graphProjection_normDet _ _ hu,
        firstSumGraph_normal_inner]
      rfl
    | some i =>
      rw [productFacetLinear_first_coordinate, coordinateProjection_normDet _ hu]
      simp [firstBlock]
  · cases i with
    | none =>
      rw [productFacetLinear_second_sum, graphProjection_normDet _ _ hu,
        secondSumGraph_normal_inner]
      rfl
    | some i =>
      rw [productFacetLinear_second_coordinate, coordinateProjection_normDet _ hu]
      simp [secondBlock]

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace

theorem solution (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (productFacetLinear i)).normDet =
      |productFunctional i u| := by
  first
    | exact OAI.ProjectionCounterexample.productFacetProjection_normDet i hu
    | exact OAI.ProjectionCounterexample.productFacetProjection_normDet
    | (apply OAI.ProjectionCounterexample.productFacetProjection_normDet <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.productFacetProjection_normDet <;> assumption)
