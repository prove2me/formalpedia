-- Prove2me | solution 1 for OAI.ProjectionCounterexample.product_projectionVolume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:38:20.960419+00:00
-- url     : https://prove2.me/submissions/525d9a4d-6e85-4052-82e1-7c4924e465d1

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductBrightness.lean:L47-L66
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.product_projectionVolume. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_measure_projected_transverse_intersection
import Theorems.Thm_OAI_ProjectionCounterexample_productFacetProjection_normDet
import Theorems.Thm_OAI_ProjectionCounterexample_product_facet_eq_affine_image
import Theorems.Thm_OAI_ProjectionCounterexample_product_facet_transverse
import Theorems.Thm_OAI_ProjectionCounterexample_real_measure_image_halfspaceBody
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_coordinates
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_halfspaceBody
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_has_positive_slope
import Theorems.Thm_OAI_ProjectionCounterexample_volume_coordinateSimplexProduct

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

-- ---- from OAI.Geometry.ProjectionBody.ProductFacets ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem productBody_eq_halfspaceBody :
    productBody = halfspaceBody productFunctional productLevel := by
  ext x
  change (firstBlock x ∈ simplex 10 ∧ secondBlock x ∈ simplex 10) ↔ _
  rw [simplex_eq_halfspaceBody]
  constructor
  · rintro ⟨hx, hy⟩ ⟨b, i⟩
    cases b
    · exact hx i
    · exact hy i
  · intro hx
    exact ⟨fun i => hx (false, i), fun i => hx (true, i)⟩

theorem blocks_eq_zero_iff (x : E 20) :
    firstBlock x = 0 ∧ secondBlock x = 0 ↔ x = 0 := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    ext i
    refine Fin.addCases (n := 10) (m := 10) (fun j => ?_) (fun j => ?_) i
    · exact congrArg (fun y : E 10 => y j) hfirst
    · exact congrArg (fun y : E 10 => y j) hsecond
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem product_has_positive_slope {u : E 20} (hu : u ≠ 0) :
    ∃ i, 0 < productFunctional i u := by
  by_cases hfirst : firstBlock u = 0
  · have hsecond : secondBlock u ≠ 0 := by
      intro hsecond
      exact hu ((blocks_eq_zero_iff u).mp ⟨hfirst, hsecond⟩)
    obtain ⟨i, hi⟩ := simplex_has_positive_slope hsecond
    exact ⟨(true, i), hi⟩
  · obtain ⟨i, hi⟩ := simplex_has_positive_slope hfirst
    exact ⟨(false, i), hi⟩

theorem product_functional_balance (u : E 20) :
    ∑ i, productFunctional i u = 0 := by
  simp [Fintype.sum_prod_type]

theorem product_absolute_slopes (u : E 20) :
    ∑ i, |productFunctional i u| =
      ((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
      ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) := by
  simp [Fintype.sum_prod_type, add_comm]

end ProjectionCounterexample

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

end DiagonalZonotope

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

/-- Product-simplex volume in the canonical Euclidean coordinates. -/
theorem volume_euclideanSimplexProduct (p q : ℕ) :
    volume {x : EuclideanSpace ℝ (Fin (p + q)) |
      ((∀ i : Fin p, 0 ≤ x (Fin.castAdd q i)) ∧
        ∑ i : Fin p, x (Fin.castAdd q i) ≤ 1) ∧
      ((∀ i : Fin q, 0 ≤ x (Fin.natAdd p i)) ∧
        ∑ i : Fin q, x (Fin.natAdd p i) ≤ 1)} =
      ENNReal.ofReal (1 / ((p.factorial : ℝ) * (q.factorial : ℝ))) := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (p + q))).symm.measure_preimage_equiv]
  exact volume_coordinateSimplexProduct p q

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

-- ---- from OAI.Geometry.ProjectionBody.ProductVolumes ----
namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

theorem volume_productFacetDomain (b : Bool) :
    volume (productFacetDomain b) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by
  cases b
  · simpa only [productFacetDomain, simplex_eq_coordinates, Set.preimage,
      Set.mem_prod, Set.mem_ofPred_eq, DiagonalZonotope.finAddEquivProd_apply,
      WithLp.ofLp_toLp] using
      volume_euclideanSimplexProduct 9 10
  · simpa only [productFacetDomain, simplex_eq_coordinates, Set.preimage,
      Set.mem_prod, Set.mem_ofPred_eq, DiagonalZonotope.finAddEquivProd_apply, WithLp.ofLp_toLp,
      mul_comm] using
      volume_euclideanSimplexProduct 10 9

theorem productFacetDomain_compact (b : Bool) : IsCompact (productFacetDomain b) := by
  cases b
  · exact (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).toHomeomorph.isCompact_preimage.mpr
      ((simplex_compact 9).prod (simplex_compact 10))
  · exact (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).toHomeomorph.isCompact_preimage.mpr
      ((simplex_compact 10).prod (simplex_compact 9))

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductBrightness ----
namespace OAI

noncomputable section
open Set MeasureTheory Measure

namespace ProjectionCounterexample

theorem product_projected_facet_volume (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    μHE[19] (project u '' boundingFace productFunctional productLevel i) =
      ENNReal.ofReal ((1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) *
        |productFunctional i u|) := by
  rw [product_facet_eq_affine_image]
  have h := measure_projected_affine_chart (productFacetLinear i)
    (productFacetCenter i) (project u).toLinearMap (productFacetDomain i.1)
  simp only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] at h
  rw [h, productFacetProjection_normDet i hu, volume_productFacetDomain,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

theorem product_projected_facet_measurable
    (i : Bool × Option (Fin 10)) (u : E 20) :
    MeasurableSet (project u '' boundingFace productFunctional productLevel i) := by
  rw [product_facet_eq_affine_image]
  apply IsCompact.measurableSet
  apply IsCompact.image _ (project u).continuous
  apply (productFacetDomain_compact i.1).image
  exact continuous_const.add (productFacetLinear i).continuous_of_finiteDimensional

theorem product_projected_facet_intersection_null
    (i j : Bool × Option (Fin 10)) (hij : i ≠ j) (u : E 20) :
    μHE[19] (project u ''
      (boundingFace productFunctional productLevel i ∩
        boundingFace productFunctional productLevel j)) = 0 := by
  have hS : boundingFace productFunctional productLevel i ⊆
      (fun x => productFacetCenter i + productFacetLinear i x) '' (univ : Set (E 19)) := by
    rw [product_facet_eq_affine_image]
    exact Set.image_mono (subset_univ _)
  simpa only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] using
    measure_projected_transverse_intersection (productFacetLinear i)
      (productFacetCenter i) (project u).toLinearMap (productFunctional j) (productLevel j)
      _ _ hS (fun _ h => h.2) (product_facet_transverse i j hij)

/-- Actual orthogonal projection volume of the twenty-dimensional product body. -/
theorem product_projectionVolume {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume productBody u =
      (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
        ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|)) /
      (2 * ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h := real_measure_image_halfspaceBody
    productFunctional productLevel (project u).toLinearMap μHE[19]
    (project_self u) (product_has_positive_slope hu0) (project_ker u)
    (fun i => product_projected_facet_measurable i u)
    (fun i j hij => product_projected_facet_intersection_null i j hij u)
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) (by positivity)
    (product_functional_balance u) (fun i => product_projected_facet_volume i hu)
  rw [← productBody_eq_halfspaceBody, product_absolute_slopes] at h
  simp only [ContinuousLinearMap.coe_coe] at h
  unfold projectionVolume
  change (μHE[19] (project u '' productBody)).toReal = _
  rw [h]
  ring

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set MeasureTheory Measure

theorem solution {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume productBody u =
      (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
        ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|)) /
      (2 * ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by
  first
    | exact OAI.ProjectionCounterexample.product_projectionVolume hu
    | exact OAI.ProjectionCounterexample.product_projectionVolume
    | (apply OAI.ProjectionCounterexample.product_projectionVolume <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.product_projectionVolume <;> assumption)
