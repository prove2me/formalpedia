-- Prove2me | solution 1 for OAI.ProjectionCounterexample.unit_support_halfspaces_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:40:01.638093+00:00
-- url     : https://prove2.me/submissions/b76a4802-2d70-4153-89f3-a00a87a5b991

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/UnitSupport.lean:L11-L37
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.unit_support_halfspaces_eq. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.UnitSupport ----
namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- For a positively homogeneous support bound, unit directions determine all
directions. This connects the unit-sphere definition with an
explicit zonotope's halfspace description. -/
theorem unit_support_halfspaces_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (hzero : 0 ≤ f 0)
    (hscale : ∀ (a : ℝ), 0 ≤ a → ∀ u, f (a • u) = a * f u) :
    {x : V | ∀ u, ‖u‖ = 1 → ⟪u, x⟫ ≤ f u} =
      {x : V | ∀ u, ⟪u, x⟫ ≤ f u} := by
  ext x
  constructor
  · intro hx u
    by_cases hu : u = 0
    · simpa [hu] using hzero
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    let v : V := ‖u‖⁻¹ • u
    have hv : ‖v‖ = 1 := by
      simp [v, norm_smul, hnorm]
    have huv : ‖u‖ • v = u := by
      simp [v, smul_smul, hnorm]
    calc
      ⟪u, x⟫ = ‖u‖ * ⟪v, x⟫ := by
        rw [← real_inner_smul_left, huv]
      _ ≤ ‖u‖ * f v := mul_le_mul_of_nonneg_left (hx v hv) (norm_nonneg u)
      _ = f u := by rw [← hscale ‖u‖ (norm_nonneg u) v, huv]
  · intro hx u _
    exact hx u

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem solution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (hzero : 0 ≤ f 0)
    (hscale : ∀ (a : ℝ), 0 ≤ a → ∀ u, f (a • u) = a * f u) :
    {x : V | ∀ u, ‖u‖ = 1 → ⟪u, x⟫ ≤ f u} =
      {x : V | ∀ u, ⟪u, x⟫ ≤ f u} := by
  first
    | exact OAI.ProjectionCounterexample.unit_support_halfspaces_eq f hzero hscale
    | exact OAI.ProjectionCounterexample.unit_support_halfspaces_eq
    | (apply OAI.ProjectionCounterexample.unit_support_halfspaces_eq <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.unit_support_halfspaces_eq <;> assumption)
