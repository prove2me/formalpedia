-- Prove2me | solution 1 for OAI.ProjectionCounterexample.real_measure_image_halfspaceBody
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:36:13.41284+00:00
-- url     : https://prove2.me/submissions/74a6672b-f56a-4cbc-84fa-e807d620f7fe

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/BrightnessSum.lean:L16-L42
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.real_measure_image_halfspaceBody. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_image_visible_faces_inter
import Theorems.Thm_OAI_ProjectionCounterexample_ray_reaches_visible_face
import Theorems.Thm_OAI_ProjectionCounterexample_sum_positive_eq_half_sum_abs

-- ---- from OAI.Geometry.ProjectionBody.FacetCover ----
namespace OAI

/-! Finite-halfspace geometry underlying the visible-facet projection formula. -/

noncomputable section
open Set

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The projected body is covered by the projections of its visible faces. -/
theorem image_halfspaceBody_eq_visible_faces
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u) :
    q '' halfspaceBody a b =
      ⋃ i : {i : ι // 0 < a i u}, q '' boundingFace a b i.1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, i, _, hiu, hface⟩ := ray_reaches_visible_face a b hy hu
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hiu⟩, y + t • u, hface, ?_⟩
    simp [map_add, map_smul, hqu]
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨y, hy.1, rfl⟩

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.FacetMeasure ----
namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace W]

/-- Finite additivity for shadows of visible faces. The geometric hypotheses
are explicit: the later applications must prove measurability and nullity of
the projected intersections. No facet-volume formula is assumed here. -/
theorem measure_image_halfspaceBody_eq_sum_visible
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W) (μ : Measure W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u)
    (hker : LinearMap.ker q = Submodule.span ℝ {u})
    (hmeas : ∀ i, MeasurableSet (q '' boundingFace a b i))
    (hnull : ∀ i j, i ≠ j →
      μ (q '' (boundingFace a b i ∩ boundingFace a b j)) = 0) :
    μ (q '' halfspaceBody a b) =
      ∑ i : {i : ι // 0 < a i u}, μ (q '' boundingFace a b i.1) := by
  classical
  rw [image_halfspaceBody_eq_visible_faces a b q hqu hu]
  have hd : Pairwise (fun i j : {i : ι // 0 < a i u} =>
      AEDisjoint μ (q '' boundingFace a b i.1) (q '' boundingFace a b j.1)) := by
    intro i j hij
    change μ ((q '' boundingFace a b i.1) ∩ (q '' boundingFace a b j.1)) = 0
    rw [image_visible_faces_inter a b q hker i.2 j.2]
    exact hnull i j (fun h => hij (Subtype.ext h))
  rw [measure_iUnion₀ hd (fun i => (hmeas i.1).nullMeasurableSet), tsum_fintype]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.BrightnessSum ----
namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace W]

/-- Convert the genuine facet-measure sum to the balanced absolute-slope formula.
Every geometric input, including each projected facet measure, remains explicit. -/
theorem real_measure_image_halfspaceBody
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W) (μ : Measure W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u)
    (hker : LinearMap.ker q = Submodule.span ℝ {u})
    (hmeas : ∀ i, MeasurableSet (q '' boundingFace a b i))
    (hnull : ∀ i j, i ≠ j →
      μ (q '' (boundingFace a b i ∩ boundingFace a b j)) = 0)
    (c : ℝ) (hc : 0 ≤ c) (hbalance : ∑ i, a i u = 0)
    (hfacet : ∀ i, μ (q '' boundingFace a b i) = ENNReal.ofReal (c * |a i u|)) :
    (μ (q '' halfspaceBody a b)).toReal = c * (∑ i, |a i u|) / 2 := by
  classical
  rw [measure_image_halfspaceBody_eq_sum_visible a b q μ hqu hu hker hmeas hnull]
  simp_rw [hfacet]
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg hc (abs_nonneg _))]
  have hs : (∑ i : {i : ι // 0 < a i u}, |a i.1 u|) =
      (∑ i with 0 < a i u, a i u) := by
    calc
      (∑ i : {i : ι // 0 < a i u}, |a i.1 u|) =
          ∑ i : {i : ι // 0 < a i u}, a i.1 u := by
        apply Finset.sum_congr rfl
        intro i _
        exact abs_of_pos i.2
      _ = _ := (Finset.sum_subtype _ (by simp) (fun i => a i u)).symm
  rw [← Finset.mul_sum, hs, sum_positive_eq_half_sum_abs _ hbalance, mul_div_assoc]

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set MeasureTheory
variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace W]

theorem solution
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W) (μ : Measure W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u)
    (hker : LinearMap.ker q = Submodule.span ℝ {u})
    (hmeas : ∀ i, MeasurableSet (q '' boundingFace a b i))
    (hnull : ∀ i j, i ≠ j →
      μ (q '' (boundingFace a b i ∩ boundingFace a b j)) = 0)
    (c : ℝ) (hc : 0 ≤ c) (hbalance : ∑ i, a i u = 0)
    (hfacet : ∀ i, μ (q '' boundingFace a b i) = ENNReal.ofReal (c * |a i u|)) :
    (μ (q '' halfspaceBody a b)).toReal = c * (∑ i, |a i u|) / 2 := by
  first
    | exact OAI.ProjectionCounterexample.real_measure_image_halfspaceBody a b q μ hqu hu hker hmeas hnull c hc hbalance hfacet
    | exact OAI.ProjectionCounterexample.real_measure_image_halfspaceBody
    | (apply OAI.ProjectionCounterexample.real_measure_image_halfspaceBody <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.real_measure_image_halfspaceBody <;> assumption)
