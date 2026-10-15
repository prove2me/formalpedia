-- Prove2me | solution 1 for OAI.ProjectionCounterexample.projectionBody_eq_productZonotope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:41:53.887442+00:00
-- url     : https://prove2.me/submissions/4726b976-0030-49b6-b145-b833d6496f75

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductZonotopeBridge.lean:L27-L50
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.projectionBody_eq_productZonotope. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductZonotopeBridge
import Theorems.Thm_OAI_DiagonalZonotope_euclideanProduct_eq_halfspaces
import Theorems.Thm_OAI_ProjectionCounterexample_unit_support_halfspaces_eq

-- ---- from OAI.Geometry.Zonotope.Scaling ----
namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma support_value_smul (u : ι → ℝ) (c : ℝ) :
    ((∑ i, |(c • u) i|) + |∑ i, (c • u) i|) / 2 =
      |c| * (((∑ i, |u i|) + |∑ i, u i|) / 2) := by
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]
  rw [← mul_add, mul_div_assoc]

end DiagonalZonotope

end

end OAI

-- ---- from OAI.Geometry.Zonotope.Euclidean ----
namespace OAI

/-! Coordinate and Euclidean versions of the explicit centered zonotope. -/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

lemma support_smul (u : ι → ℝ) (a : ℝ) : support (a • u) = |a| * support u :=
  support_value_smul u a

end DiagonalZonotope

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductZonotopeBridge ----
namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

lemma blockSupport_zero (n m : ℕ) : blockSupport (0 : E (n + m)) = 0 := by
  simp [blockSupport, DiagonalZonotope.support]

lemma blockSupport_smul {n m : ℕ} (u : E (n + m)) (a : ℝ) :
    blockSupport (a • u) = |a| * blockSupport u := by
  simp only [blockSupport, map_smul, Prod.smul_fst, Prod.smul_snd]
  change DiagonalZonotope.support (a • WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
      DiagonalZonotope.support (a • WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2) = _
  rw [DiagonalZonotope.support_smul, DiagonalZonotope.support_smul, mul_add]

/-- A proved block brightness formula identifies the product projection zonotope. -/
theorem projectionBody_eq_productZonotope {n m : ℕ} (P : Set (E (n + m)))
    (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E (n + m), ‖u‖ = 1 → projectionVolume P u = c * blockSupport u) :
    projectionBody P = DiagonalZonotope.euclideanProduct n m c := by
  calc
    projectionBody P = {x : E (n + m) | ∀ u : E (n + m), ‖u‖ = 1 →
        ⟪u, x⟫ ≤ c * blockSupport u} := by
      ext x
      constructor
      · intro hx u hu
        rw [← hbrightness u hu]
        exact hx u hu
      · intro hx u hu
        rw [hbrightness u hu]
        exact hx u hu
    _ = {x : E (n + m) | ∀ u : E (n + m), ⟪u, x⟫ ≤ c * blockSupport u} := by
      apply unit_support_halfspaces_eq
      · simp [blockSupport_zero]
      · intro a ha u
        rw [blockSupport_smul, abs_of_nonneg ha]
        ring
    _ = DiagonalZonotope.euclideanProduct n m c :=
      (DiagonalZonotope.euclideanProduct_eq_halfspaces n m c hc).symm

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem solution {n m : ℕ} (P : Set (E (n + m)))
    (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E (n + m), ‖u‖ = 1 → projectionVolume P u = c * blockSupport u) :
    projectionBody P = DiagonalZonotope.euclideanProduct n m c := by
  first
    | exact OAI.ProjectionCounterexample.projectionBody_eq_productZonotope P c hc hbrightness
    | exact OAI.ProjectionCounterexample.projectionBody_eq_productZonotope
    | (apply OAI.ProjectionCounterexample.projectionBody_eq_productZonotope <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.projectionBody_eq_productZonotope <;> assumption)
