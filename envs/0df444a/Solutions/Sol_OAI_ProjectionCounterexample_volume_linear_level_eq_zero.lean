-- Prove2me | solution 1 for OAI.ProjectionCounterexample.volume_linear_level_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:33:25.044405+00:00
-- url     : https://prove2.me/submissions/efc9f70a-cb6c-4b8a-8684-63f82b27c029

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/NullHyperplane.lean:L10-L29
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.volume_linear_level_eq_zero. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.NullHyperplane ----
namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

/-- Every level set of a nonzero real linear functional has zero ambient volume. -/
theorem volume_linear_level_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    [Measure.IsAddHaarMeasure (volume : Measure V)]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {x : V | f x = c} = 0 := by
  let H : AffineSubspace ℝ V := (affineSpan ℝ ({c} : Set ℝ)).comap f.toAffineMap
  have hmem (x : V) : x ∈ H ↔ f x = c := by
    simp [H]
  have hproper : H ≠ ⊤ := by
    intro htop
    have heq (x : V) : f x = c := (hmem x).mp (by rw [htop]; trivial)
    have hc : c = 0 := by simpa using (heq 0).symm
    apply hf
    ext x
    simpa [hc] using heq x
  have hset : (H : Set V) = {x : V | f x = c} := Set.ext hmem
  rw [← hset]
  exact Measure.addHaar_affineSubspace volume H hproper

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set MeasureTheory

theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    [Measure.IsAddHaarMeasure (volume : Measure V)]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {x : V | f x = c} = 0 := by
  first
    | exact OAI.ProjectionCounterexample.volume_linear_level_eq_zero f hf c
    | exact OAI.ProjectionCounterexample.volume_linear_level_eq_zero
    | (apply OAI.ProjectionCounterexample.volume_linear_level_eq_zero <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.volume_linear_level_eq_zero <;> assumption)
