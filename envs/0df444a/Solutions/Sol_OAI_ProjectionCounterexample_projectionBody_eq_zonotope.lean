-- Prove2me | solution 1 for OAI.ProjectionCounterexample.projectionBody_eq_zonotope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:40:57.936259+00:00
-- url     : https://prove2.me/submissions/6b6567c9-42f0-4f9e-a118-5988f2275ae0

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ZonotopeBridge.lean:L18-L43
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.projectionBody_eq_zonotope. The node keeps its source
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
import Theorems.Thm_OAI_DiagonalZonotope_scaled_centered_eq_support_halfspaces
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

-- ---- from OAI.Geometry.ProjectionBody.ZonotopeBridge ----
namespace OAI

/-!
Generic bridge from a *proved* directional projection-volume formula to the
explicit zonotope. The brightness formula is an explicit hypothesis of these
helper lemmas; no final counterexample theorem assumes it.
-/
noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- A unit-direction brightness formula identifies the actual projection body. -/
theorem projectionBody_eq_zonotope {d : ℕ} (P : Set (E d)) (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E d, ‖u‖ = 1 →
      projectionVolume P u = c * DiagonalZonotope.support (WithLp.ofLp u)) :
    projectionBody P = DiagonalZonotope.euclidean c := by
  calc
    projectionBody P = {x : E d | ∀ u : E d, ‖u‖ = 1 →
        ⟪u, x⟫ ≤ c * DiagonalZonotope.support (WithLp.ofLp u)} := by
      ext x
      constructor
      · intro hx u hu
        rw [← hbrightness u hu]
        exact hx u hu
      · intro hx u hu
        rw [hbrightness u hu]
        exact hx u hu
    _ = {x : E d | ∀ u : E d,
        ⟪u, x⟫ ≤ c * DiagonalZonotope.support (WithLp.ofLp u)} := by
      apply unit_support_halfspaces_eq
      · simp [DiagonalZonotope.support]
      · intro a ha u
        change c * DiagonalZonotope.support (a • WithLp.ofLp u) = _
        rw [DiagonalZonotope.support_smul, abs_of_nonneg ha]
        ring
    _ = DiagonalZonotope.euclidean c :=
      (DiagonalZonotope.euclidean_eq_halfspaces c hc).symm

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem solution {d : ℕ} (P : Set (E d)) (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E d, ‖u‖ = 1 →
      projectionVolume P u = c * DiagonalZonotope.support (WithLp.ofLp u)) :
    projectionBody P = DiagonalZonotope.euclidean c := by
  first
    | exact OAI.ProjectionCounterexample.projectionBody_eq_zonotope P c hc hbrightness
    | exact OAI.ProjectionCounterexample.projectionBody_eq_zonotope
    | (apply OAI.ProjectionCounterexample.projectionBody_eq_zonotope <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.projectionBody_eq_zonotope <;> assumption)
