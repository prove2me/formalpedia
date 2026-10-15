-- Prove2me | solution 1 for OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:18:38.559235+00:00
-- url     : https://prove2.me/submissions/35e44222-0301-4405-b8af-1a43b8cfe139

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Scaling.lean:L29-L48
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces. The node keeps its source
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
import Theorems.Thm_OAI_DiagonalZonotope_centered_eq_support_halfspaces
import Theorems.Thm_OAI_DiagonalZonotope_centered_support_le

-- ---- from OAI.Geometry.Zonotope.Scaling ----
namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma coordinate_pairing_smul (u x : ι → ℝ) (c : ℝ) :
    (∑ i, u i * (c • x) i) = c * ∑ i, u i * x i := by
  calc
    _ = ∑ i, c * (u i * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_left_comm (u i) c (x i)
    _ = _ := by rw [Finset.mul_sum]

/-- Positive scalar images of the centered zonotope have the scaled support inequalities. -/
theorem scaled_centered_eq_support_halfspaces (c : ℝ) (hc : 0 < c) :
    (fun y : ι → ℝ => c • y) '' centered =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        c * (((∑ i, |u i|) + |∑ i, u i|) / 2)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ u
    rw [coordinate_pairing_smul]
    exact mul_le_mul_of_nonneg_left (centered_support_le u y hy) hc.le
  · intro hx
    refine ⟨c⁻¹ • x, ?_, ?_⟩
    · rw [centered_eq_support_halfspaces]
      intro u
      rw [coordinate_pairing_smul]
      have h := mul_le_mul_of_nonneg_left (hx u) (inv_nonneg.mpr hc.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
    · funext i
      change c * (c⁻¹ * x i) = x i
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

end DiagonalZonotope

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalZonotope
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (c : ℝ) (hc : 0 < c) :
    (fun y : ι → ℝ => c • y) '' centered =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        c * (((∑ i, |u i|) + |∑ i, u i|) / 2)} := by
  first
    | exact OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces c hc
    | exact OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces
    | (apply OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces <;> assumption)
    | (intros; apply OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces <;> assumption)
