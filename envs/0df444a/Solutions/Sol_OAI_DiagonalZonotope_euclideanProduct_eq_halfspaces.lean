-- Prove2me | solution 1 for OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:19:18.343908+00:00
-- url     : https://prove2.me/submissions/a3920ae6-5865-40f8-b4ad-a7b7c3a05aae

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Product.lean:L47-L75
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces. The node keeps its source
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
import Theorems.Thm_OAI_DiagonalZonotope_scaled_centered_eq_support_halfspaces

-- ---- from OAI.Geometry.Zonotope.Euclidean ----
namespace OAI

/-! Coordinate and Euclidean versions of the explicit centered zonotope. -/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

lemma support_zero : support (0 : ι → ℝ) = 0 := by simp [support]

lemma inner_eq_coordinates (u x : EuclideanSpace ℝ ι) :
    ⟪u, x⟫ = ∑ i, u i * x i := by
  simp only [PiLp.inner_apply, Real.inner_apply]

omit [Fintype ι] in
lemma mem_euclidean_iff (c : ℝ) (x : EuclideanSpace ℝ ι) :
    x ∈ euclidean c ↔ WithLp.ofLp x ∈ (fun y : ι → ℝ => c • y) '' centered := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hx
    exact ⟨WithLp.ofLp x, hx, rfl⟩

/-- All directional inequalities characterize this concrete Euclidean body. -/
theorem euclidean_eq_halfspaces [DecidableEq ι] (c : ℝ) (hc : 0 < c) :
    (euclidean c : Set (EuclideanSpace ℝ ι)) =
      {x | ∀ u : EuclideanSpace ℝ ι, ⟪u, x⟫ ≤ c * support (WithLp.ofLp u)} := by
  ext x
  rw [mem_euclidean_iff, scaled_centered_eq_support_halfspaces c hc]
  constructor
  · intro hx u
    simpa only [inner_eq_coordinates, support] using hx (WithLp.ofLp u)
  · intro hx u
    simpa only [inner_eq_coordinates, support] using hx (WithLp.toLp 2 u)

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

/-- Product support is the sum of the two independently attainable supports. -/
theorem euclideanProduct_eq_halfspaces (n m : ℕ) (c : ℝ) (hc : 0 < c) :
    euclideanProduct n m c =
      {x | ∀ u : EuclideanSpace ℝ (Fin (n + m)), ⟪u, x⟫ ≤ c *
        (support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
         support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2))} := by
  ext x
  constructor
  · intro hx u
    obtain ⟨hx₁, hx₂⟩ := hx
    rw [euclidean_eq_halfspaces c hc] at hx₁ hx₂
    rw [inner_finAdd, mul_add]
    exact add_le_add (hx₁ _) (hx₂ _)
  · intro hx
    change (EuclideanSpace.finAddEquivProd x).1 ∈ euclidean c ∧
      (EuclideanSpace.finAddEquivProd x).2 ∈ euclidean c
    constructor
    · rw [euclidean_eq_halfspaces c hc]
      intro u
      have h := hx (EuclideanSpace.finAddEquivProd.symm (u, 0))
      rw [inner_finAdd] at h
      simpa only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
        add_zero, WithLp.ofLp_zero, support_zero] using h
    · rw [euclidean_eq_halfspaces c hc]
      intro u
      have h := hx (EuclideanSpace.finAddEquivProd.symm (0, u))
      rw [inner_finAdd] at h
      simpa only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
        zero_add, WithLp.ofLp_zero, support_zero] using h

end DiagonalZonotope

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalZonotope
open Set
open scoped RealInnerProductSpace

theorem solution (n m : ℕ) (c : ℝ) (hc : 0 < c) :
    euclideanProduct n m c =
      {x | ∀ u : EuclideanSpace ℝ (Fin (n + m)), ⟪u, x⟫ ≤ c *
        (support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
         support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2))} := by
  first
    | exact OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces n m c hc
    | exact OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces
    | (apply OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces <;> assumption)
    | (intros; apply OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces <;> assumption)
