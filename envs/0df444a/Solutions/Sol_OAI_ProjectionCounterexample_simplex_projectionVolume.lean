-- Prove2me | solution 1 for OAI.ProjectionCounterexample.simplex_projectionVolume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:37:03.913714+00:00
-- url     : https://prove2.me/submissions/6810105d-c988-466b-ac4c-bc894d8cddfc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexBrightness.lean:L75-L93
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.simplex_projectionVolume. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_coordinate_facet_eq_image
import Theorems.Thm_OAI_ProjectionCounterexample_graphProjection_normDet
import Theorems.Thm_OAI_ProjectionCounterexample_measure_projected_transverse_intersection
import Theorems.Thm_OAI_ProjectionCounterexample_real_measure_image_halfspaceBody
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_coordinates
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_halfspaceBody
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_facet_transverse
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_has_positive_slope
import Theorems.Thm_OAI_ProjectionCounterexample_sum_facet_eq_image
import Theorems.Thm_OAI_ProjectionCounterexample_volume_coordinateSimplex

-- ---- from OAI.Geometry.ProjectionBody.ConvexGeometry ----
namespace OAI

open Set

namespace ProjectionCounterexample

noncomputable section

theorem simplex_compact (d : ℕ) : IsCompact (simplex d) :=
  ((finite_range _).insert 0).isCompact_convexHull ℝ

end

end ProjectionCounterexample

end OAI

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacets ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem simplex_functional_balance {d : ℕ} (u : E d) :
    ∑ i, simplexFunctional d i u = 0 := by
  simp [Fintype.sum_option, Finset.sum_neg_distrib]

theorem simplex_absolute_slopes {d : ℕ} (u : E d) :
    ∑ i, |simplexFunctional d i u| = (∑ i, |u i|) + |∑ i, u i| := by
  simp [Fintype.sum_option, add_comm]

theorem simplex_boundingFace_coordinate {d : ℕ} (i : Fin d) :
    boundingFace (simplexFunctional d) simplexLevel (some i) =
      {x ∈ simplex d | x i = 0} := by
  ext x
  simp [boundingFace, ← simplex_eq_halfspaceBody, simplexLevel]

theorem simplex_boundingFace_sum (d : ℕ) :
    boundingFace (simplexFunctional d) simplexLevel none =
      {x ∈ simplex d | ∑ i, x i = 1} := by
  ext x
  simp [boundingFace, ← simplex_eq_halfspaceBody, simplexLevel]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacetCharts ----
namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem simplexFacetChart_none (n : ℕ) (x : E n) :
    simplexFacetCenter n none + simplexFacetLinear n none x = sumFacetMap n x := by
  ext j
  induction j using Fin.lastCases
  · simp [simplexFacetCenter, simplexFacetLinear, graphLinear, sub_eq_add_neg]
  · simp [simplexFacetCenter, simplexFacetLinear, graphLinear, insertZero,
      Fin.insertNth_last']

theorem simplex_facet_eq_affine_image (n : ℕ) (i : Option (Fin (n + 1))) :
    boundingFace (simplexFunctional (n + 1)) simplexLevel i =
      (fun x => simplexFacetCenter n i + simplexFacetLinear n i x) '' simplex n := by
  cases i with
  | none =>
    simp_rw [simplex_boundingFace_sum, simplexFacetChart_none]
    exact sum_facet_eq_image n
  | some i =>
    rw [simplex_boundingFace_coordinate, coordinate_facet_eq_image]
    simp [simplexFacetCenter, simplexFacetLinear]

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

-- ---- from OAI.Geometry.ProjectionBody.SimplexVolume ----
namespace OAI

/-!
# Volumes of standard simplices and their products

The simplex-volume calculation below uses Tonelli's theorem and induction on the
dimension.  At first coordinate `t`, the remaining section is a simplex of radius
`r - t`; its volume is integrated over `0 ≤ t ≤ r`.  The Euclidean versions use
the measure-preserving equivalence between coordinate space and `EuclideanSpace`.
The product formula is proved using the product Lebesgue measure under the
canonical splitting of `Fin (p + q)`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProjectionCounterexample

/-- The standard simplex has ordinary Lebesgue volume `1 / n!`. -/
theorem volume_unit_coordinateSimplex (n : ℕ) :
    volume (coordinateSimplex n 1) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  simpa using volume_coordinateSimplex n 1 zero_le_one

/-- The same volume statement in Euclidean space with its canonical Euclidean measure. -/
theorem volume_unit_euclideanSimplex (n : ℕ) :
    volume {x : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hs : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    measurability
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage hs.nullMeasurableSet]
  exact volume_unit_coordinateSimplex n

end ProjectionCounterexample

end OAI

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

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProjectionKernel ----
namespace OAI

noncomputable section

namespace ProjectionCounterexample

theorem project_ker {d : ℕ} (u : E d) :
    (project u).toLinearMap.ker = Submodule.span ℝ {u} := by
  change (ℝ ∙ u)ᗮ.starProjection.ker = ℝ ∙ u
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.SimplexBrightness ----
namespace OAI

noncomputable section
open Set MeasureTheory Measure
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem volume_simplex (n : ℕ) :
    volume (simplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [simplex_eq_coordinates]
  exact volume_unit_euclideanSimplex n

theorem simplexFacetProjection_normDet {n : ℕ} (i : Option (Fin (n + 1)))
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (simplexFacetLinear n i)).normDet =
      |simplexFunctional (n + 1) i u| := by
  cases i with
  | none =>
    change ((project u).toLinearMap.comp
      (graphLinear (Fin.last n) (allOnes n))).normDet = _
    rw [graphProjection_normDet _ _ hu]
    have hnormal : graphNormal (Fin.last n) (allOnes n) = allOnes (n + 1) := by
      ext j
      induction j using Fin.lastCases <;>
        simp [graphNormal, insertZero, Fin.insertNth_last']
    simp [hnormal]
  | some i =>
    change ((project u).toLinearMap.comp (insertZero i).toLinearMap).normDet = _
    rw [coordinateProjection_normDet i hu]
    simp

theorem simplex_projected_facet_volume {n : ℕ} (i : Option (Fin (n + 1)))
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    μHE[n] (project u '' boundingFace (simplexFunctional (n + 1)) simplexLevel i) =
      ENNReal.ofReal ((1 / (n.factorial : ℝ)) * |simplexFunctional (n + 1) i u|) := by
  rw [simplex_facet_eq_affine_image]
  have h := measure_projected_affine_chart (simplexFacetLinear n i)
    (simplexFacetCenter n i) (project u).toLinearMap (simplex n)
  simp only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] at h
  rw [h, simplexFacetProjection_normDet i hu, volume_simplex,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

theorem simplex_projected_facet_measurable {n : ℕ}
    (i : Option (Fin (n + 1))) (u : E (n + 1)) :
    MeasurableSet (project u '' boundingFace (simplexFunctional (n + 1)) simplexLevel i) := by
  rw [simplex_facet_eq_affine_image]
  apply IsCompact.measurableSet
  apply IsCompact.image _ (project u).continuous
  apply (simplex_compact n).image
  exact continuous_const.add (simplexFacetLinear n i).continuous_of_finiteDimensional

theorem simplex_projected_facet_intersection_null {n : ℕ} (hn : 0 < n)
    (i j : Option (Fin (n + 1))) (hij : i ≠ j) (u : E (n + 1)) :
    μHE[n] (project u ''
      (boundingFace (simplexFunctional (n + 1)) simplexLevel i ∩
        boundingFace (simplexFunctional (n + 1)) simplexLevel j)) = 0 := by
  have hS : boundingFace (simplexFunctional (n + 1)) simplexLevel i ⊆
      (fun x => simplexFacetCenter n i + simplexFacetLinear n i x) '' (univ : Set (E n)) := by
    rw [simplex_facet_eq_affine_image]
    exact Set.image_mono (subset_univ _)
  simpa only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] using
    measure_projected_transverse_intersection (simplexFacetLinear n i)
      (simplexFacetCenter n i) (project u).toLinearMap
      (simplexFunctional (n + 1) j) (simplexLevel j) _ _ hS
      (fun _ h => h.2) (simplex_facet_transverse hn i j hij)

/-- Actual orthogonal projection volume of the convex-hull standard simplex. -/
theorem simplex_projectionVolume {n : ℕ} (hn : 0 < n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    projectionVolume (simplex (n + 1)) u =
      ((∑ i, |u i|) + |∑ i, u i|) / (2 * (n.factorial : ℝ)) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h := real_measure_image_halfspaceBody
    (simplexFunctional (n + 1)) simplexLevel (project u).toLinearMap μHE[n]
    (project_self u) (simplex_has_positive_slope hu0) (project_ker u)
    (fun i => simplex_projected_facet_measurable i u)
    (fun i j hij => simplex_projected_facet_intersection_null hn i j hij u)
    (1 / (n.factorial : ℝ)) (by positivity) (simplex_functional_balance u)
    (fun i => simplex_projected_facet_volume i hu)
  rw [← simplex_eq_halfspaceBody, simplex_absolute_slopes] at h
  simp only [ContinuousLinearMap.coe_coe] at h
  unfold projectionVolume
  simp only [Nat.add_sub_cancel]
  rw [h]
  ring

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set MeasureTheory Measure
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (hn : 0 < n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    projectionVolume (simplex (n + 1)) u =
      ((∑ i, |u i|) + |∑ i, u i|) / (2 * (n.factorial : ℝ)) := by
  first
    | exact OAI.ProjectionCounterexample.simplex_projectionVolume hn hu
    | exact OAI.ProjectionCounterexample.simplex_projectionVolume
    | (apply OAI.ProjectionCounterexample.simplex_projectionVolume <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.simplex_projectionVolume <;> assumption)
