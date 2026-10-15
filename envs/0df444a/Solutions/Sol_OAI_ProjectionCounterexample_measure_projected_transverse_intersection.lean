-- Prove2me | solution 1 for OAI.ProjectionCounterexample.measure_projected_transverse_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:34:17.564355+00:00
-- url     : https://prove2.me/submissions/828c7bb1-214d-4e85-96ed-0cde353bfca7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/AffineChartMeasure.lean:L31-L50
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.measure_projected_transverse_intersection. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_volume_linear_level_eq_zero

-- ---- from OAI.Geometry.ProjectionBody.AffineChartMeasure ----
namespace OAI

noncomputable section
open Set MeasureTheory Measure

namespace ProjectionCounterexample

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The volume of a projected affine chart, with its genuine linear Jacobian. -/
theorem measure_projected_affine_chart (L : U →ₗ[ℝ] V) (c : V)
    (q : V →ₗ[ℝ] V) (s : Set U) :
    μHE[Module.finrank ℝ U] (q '' ((fun x => c + L x) '' s)) =
      ENNReal.ofReal (q.comp L).normDet * volume s := by
  have himage : q '' ((fun x => c + L x) '' s) =
      (fun y => q c + y) '' (q.comp L '' s) := by
    simp only [Set.image_image]
    congr 1
    funext x
    exact map_add q c (L x)
  rw [himage, (isometry_add_left _).euclideanHausdorffMeasure_image,
    (q.comp L).euclideanHausdorffMeasure_image_eq_normDet_mul_volume]

/-- Intersecting a facet chart with a genuinely transverse affine equation
has zero facet-dimensional measure, including after any linear projection. -/
theorem measure_projected_transverse_intersection (L : U →ₗ[ℝ] V) (c : V)
    (q : V →ₗ[ℝ] V) (g : V →ₗ[ℝ] ℝ) (r : ℝ) (S T : Set V)
    (hS : S ⊆ (fun x => c + L x) '' (univ : Set U))
    (hT : T ⊆ {y | g y = r}) (hg : g.comp L ≠ 0) :
    μHE[Module.finrank ℝ U] (q '' (S ∩ T)) = 0 := by
  have hsub : q '' (S ∩ T) ⊆
      q '' ((fun x => c + L x) '' {x | (g.comp L) x = r - g c}) := by
    rintro z ⟨y, ⟨hyS, hyT⟩, rfl⟩
    obtain ⟨x, _, rfl⟩ := hS hyS
    refine ⟨c + L x, ⟨x, ?_, rfl⟩, rfl⟩
    have heq := hT hyT
    change g (c + L x) = r at heq
    rw [map_add] at heq
    change g (L x) = r - g c
    exact eq_sub_of_add_eq' heq
  apply measure_mono_null hsub
  rw [measure_projected_affine_chart,
    volume_linear_level_eq_zero (g.comp L) hg, mul_zero]

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set MeasureTheory Measure
variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem solution (L : U →ₗ[ℝ] V) (c : V)
    (q : V →ₗ[ℝ] V) (g : V →ₗ[ℝ] ℝ) (r : ℝ) (S T : Set V)
    (hS : S ⊆ (fun x => c + L x) '' (univ : Set U))
    (hT : T ⊆ {y | g y = r}) (hg : g.comp L ≠ 0) :
    μHE[Module.finrank ℝ U] (q '' (S ∩ T)) = 0 := by
  first
    | exact OAI.ProjectionCounterexample.measure_projected_transverse_intersection L c q g r S T hS hT hg
    | exact OAI.ProjectionCounterexample.measure_projected_transverse_intersection
    | (apply OAI.ProjectionCounterexample.measure_projected_transverse_intersection <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.measure_projected_transverse_intersection <;> assumption)
