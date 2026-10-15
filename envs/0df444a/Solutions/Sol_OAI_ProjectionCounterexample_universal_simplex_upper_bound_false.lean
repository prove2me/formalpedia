-- Prove2me | solution 1 for OAI.ProjectionCounterexample.universal_simplex_upper_bound_false
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:43:18.323295+00:00
-- url     : https://prove2.me/submissions/ba6504f3-aecb-46a5-9423-8ae76c7d130a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/Counterexample.lean:L96-L99
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ProjectionCounterexample.universal_simplex_upper_bound_false.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ProjectionCounterexample_universal_simplex_upper_bound_false) verbatim and is proved by it.
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
import Definitions.Def_OAI_Geometry_Zonotope_Determinant
import Definitions.Def_OAI_Geometry_Zonotope_Shear
import Definitions.Def_OAI_Geometry_Zonotope_Volume
import Theorems.Thm_OAI_DiagonalZonotope_mem_centered_iff
import Theorems.Thm_OAI_DiagonalZonotope_zonotope_decomposition
import Theorems.Thm_OAI_ProjectionCounterexample_product_projectionVolume
import Theorems.Thm_OAI_ProjectionCounterexample_projectionBody_eq_productZonotope
import Theorems.Thm_OAI_ProjectionCounterexample_projectionBody_eq_zonotope
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_coordinates
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_projectionVolume
import Theorems.Thm_OAI_ProjectionCounterexample_volume_coordinateSimplex
import Theorems.Thm_OAI_ProjectionCounterexample_volume_coordinateSimplexProduct

-- ---- from OAI.Geometry.ProjectionBody.ConvexGeometry ----
namespace OAI

open Set

namespace ProjectionCounterexample

noncomputable section

theorem simplex_convex (d : ℕ) : Convex ℝ (simplex d) :=
  convex_convexHull ℝ _

theorem simplex_compact (d : ℕ) : IsCompact (simplex d) :=
  ((finite_range _).insert 0).isCompact_convexHull ℝ

theorem simplex_interior_nonempty (d : ℕ) : (interior (simplex d)).Nonempty := by
  rw [(simplex_convex d).interior_nonempty_iff_affineSpan_eq_top]
  rw [simplex, affineSpan_convexHull]
  apply SetLike.coe_injective
  rw [affineSpan_insert_zero]
  have hb : (EuclideanSpace.basisFun (Fin d) ℝ : Fin d → E d) =
      (fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) := by
    funext i
    simp only [EuclideanSpace.basisFun_apply]
  have hspan : Submodule.span ℝ (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
    simpa only [OrthonormalBasis.coe_toBasis, hb] using
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq
  exact congrArg (fun S : Submodule ℝ (E d) => (S : Set (E d))) hspan

theorem productBody_eq_preimage :
    productBody = blockEquiv ⁻¹' (simplex 10 ×ˢ simplex 10) := by
  rfl

theorem productBody_compact : IsCompact productBody := by
  rw [productBody_eq_preimage]
  exact blockEquiv.toHomeomorph.isCompact_preimage.mpr
    ((simplex_compact 10).prod (simplex_compact 10))

theorem productBody_convex : Convex ℝ productBody := by
  rw [productBody_eq_preimage]
  exact ((simplex_convex 10).prod (simplex_convex 10)).linear_preimage
    blockEquiv.toLinearMap

theorem productBody_interior_nonempty : (interior productBody).Nonempty := by
  rw [productBody_eq_preimage]
  change (interior (blockEquiv.toHomeomorph ⁻¹' (simplex 10 ×ˢ simplex 10))).Nonempty
  rw [← blockEquiv.toHomeomorph.preimage_interior, interior_prod_eq]
  obtain ⟨x, hx⟩ := simplex_interior_nonempty 10
  exact ⟨blockEquiv.symm (x, x), by simpa using And.intro hx hx⟩

theorem productBody_convexBody :
    IsCompact productBody ∧ Convex ℝ productBody ∧ (interior productBody).Nonempty :=
  ⟨productBody_compact, productBody_convex, productBody_interior_nonempty⟩

end

end ProjectionCounterexample

end OAI

-- ---- from OAI.Geometry.Zonotope.Decomposition ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
The unit cube extruded by the segment from zero to the all-ones vector.
Its decomposition uses the cube and one extrusion cell for every upper facet.
The set definitions are literal subsets of a finite real coordinate space.
-/

noncomputable section
open Set

namespace DiagonalZonotope

variable {ι : Type*}

/-- The cube and an upper-facet extrusion meet only in that facet's hyperplane. -/
theorem cube_inter_cell_subset (i : ι) :
    (cube : Set (ι → ℝ)) ∩ cell i ⊆ {x | x i = 1} := by
  intro x hx
  exact le_antisymm (hx.1 i).2 hx.2.1

/-- Distinct extrusion cells meet only on a coordinate-equality hyperplane. -/
theorem cell_inter_cell_subset (i j : ι) :
    cell i ∩ cell j ⊆ {x : ι → ℝ | x i = x j} := by
  intro x hx
  exact le_antisymm (hx.2.2.2 i).2 (hx.1.2.2 j).2

section AffineCell
variable [DecidableEq ι]

end AffineCell
end DiagonalZonotope

end

end OAI

-- ---- from OAI.Geometry.Zonotope.Body ----
namespace OAI

noncomputable section
open Set
open scoped Pointwise

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

lemma isClosed_centered : IsClosed (centered : Set (ι → ℝ)) := by
  have hs : (centered : Set (ι → ℝ)) =
      {x | ∀ i, |x i| ≤ 1} ∩ {x | ∀ i j, |x i - x j| ≤ 1} := by
    ext x
    exact mem_centered_iff x
  rw [hs]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le ((continuous_apply i).sub (continuous_apply j)).abs continuous_const

lemma isCompact_centered : IsCompact (centered : Set (ι → ℝ)) := by
  apply (isCompact_Icc : IsCompact (Icc (-1 : ι → ℝ) 1)).of_isClosed_subset
    isClosed_centered
  intro x hx
  have h := (mem_centered_iff x).mp hx
  exact ⟨fun i => (abs_le.mp (h.1 i)).1, fun i => (abs_le.mp (h.1 i)).2⟩

lemma isCompact_scaled_centered (c : ℝ) :
    IsCompact ((fun y : ι → ℝ => c • y) '' centered) :=
  isCompact_centered.smul c

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

omit [Fintype ι] in
lemma mem_euclidean_iff (c : ℝ) (x : EuclideanSpace ℝ ι) :
    x ∈ euclidean c ↔ WithLp.ofLp x ∈ (fun y : ι → ℝ => c • y) '' centered := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hx
    exact ⟨WithLp.ofLp x, hx, rfl⟩

lemma isCompact_euclidean (c : ℝ) : IsCompact (euclidean c : Set (EuclideanSpace ℝ ι)) :=
  (isCompact_scaled_centered c).image (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))

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

-- ---- from OAI.Geometry.ProjectionBody.Arithmetic ----
namespace OAI

/-! Numerical consequences, to be used only after the geometric volume identities. -/

namespace ProjectionCounterexample

theorem numerical_product_ratio :
    (((11 : ℝ) * 10 ^ 10 / (Nat.factorial 10 : ℝ)) ^ 2) /
        ((21 : ℝ) * 20 ^ 20 / (Nat.factorial 20 : ℝ)) =
      (22355476 : ℝ) / 22020096 := by
  norm_num [Nat.factorial]

theorem numerical_strict_excess :
    (1 : ℝ) < (22355476 : ℝ) / 22020096 := by
  norm_num

end ProjectionCounterexample

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

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductVolumes ----
namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

theorem volume_productBody :
    volume productBody = ENNReal.ofReal (1 / ((Nat.factorial 10 : ℝ) * Nat.factorial 10)) := by
  simpa only [productBody, simplex_eq_coordinates, firstBlock, secondBlock,
    Set.mem_ofPred_eq, WithLp.ofLp_toLp] using
    volume_euclideanSimplexProduct 10 10

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.Zonotope.Volume ----
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace DiagonalZonotope

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma isCompact_cube : IsCompact (cube : Set (ι → ℝ)) := by
  rw [cube_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

omit [Fintype ι] in
lemma continuous_extrusionMap (i : ι) : Continuous (extrusionMap i : (ι → ℝ) → (ι → ℝ)) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · simpa [extrusionMap, hji] using (show Continuous (fun a : ι → ℝ => (1 : ℝ) + a i) from
      continuous_const.add (continuous_apply i))
  · simpa [extrusionMap, hji] using (show Continuous (fun a : ι → ℝ => a j + a i) from
      (continuous_apply j).add (continuous_apply i))

omit [Fintype ι] in
lemma isCompact_cell (i : ι) : IsCompact (cell i) := by
  rw [cell_eq_image_cube]
  exact isCompact_cube.image (continuous_extrusionMap i)

omit [DecidableEq ι] in
lemma volume_coordinate_hyperplane (i : ι) (r : ℝ) :
    volume {x : ι → ℝ | x i = r} = 0 := by
  exact Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i r

lemma volume_coordinate_diagonal {i j : ι} (hij : i ≠ j) :
    volume {x : ι → ℝ | x i = x j} = 0 := by
  let H : Submodule ℝ (ι → ℝ) :=
    { carrier := {x | x i = x j}
      zero_mem' := rfl
      add_mem' := by
        intro x y hx hy
        exact congrArg₂ (· + ·) hx hy
      smul_mem' := by
        intro c x hx
        exact congrArg (fun t : ℝ => c * t) hx }
  change volume (H : Set (ι → ℝ)) = 0
  apply Measure.addHaar_submodule
  intro htop
  have hmem : Pi.single i (1 : ℝ) ∈ H := by
    rw [htop]
    trivial
  change (Pi.single i (1 : ℝ) : ι → ℝ) i = (Pi.single i (1 : ℝ) : ι → ℝ) j at hmem
  simp [Ne.symm hij] at hmem

lemma cell_pairwise_aedisjoint :
    Pairwise (fun i j : ι => AEDisjoint volume (cell i) (cell j)) := by
  intro i j hij
  exact measure_mono_null (cell_inter_cell_subset i j) (volume_coordinate_diagonal hij)

omit [DecidableEq ι] in
lemma cube_aedisjoint_cells :
    AEDisjoint volume (cube : Set (ι → ℝ)) (⋃ i, cell i) := by
  change volume (cube ∩ ⋃ i, cell i) = 0
  rw [inter_iUnion]
  exact measure_iUnion_null fun i =>
    measure_mono_null (cube_inter_cell_subset i) (volume_coordinate_hyperplane i 1)

/-- Lebesgue volume of the actual cube-plus-diagonal zonotope. -/
theorem volume_zonotope :
    volume (zonotope : Set (ι → ℝ)) = (Fintype.card ι : ℝ≥0∞) + 1 := by
  rw [zonotope_decomposition]
  rw [measure_union₀ (MeasurableSet.iUnion (fun i => (isCompact_cell i).measurableSet)).nullMeasurableSet
    cube_aedisjoint_cells]
  rw [volume_cube, measure_iUnion₀ cell_pairwise_aedisjoint
    (fun i => (isCompact_cell i).measurableSet.nullMeasurableSet)]
  simp [tsum_fintype, add_comm]

/-- Translation to the center does not change the computed volume. -/
theorem volume_centered :
    volume (centered : Set (ι → ℝ)) = (Fintype.card ι : ℝ≥0∞) + 1 := by
  change volume ((fun x : ι → ℝ => x + 1) ⁻¹' zonotope) = _
  rw [measure_preimage_add_right, volume_zonotope]

end DiagonalZonotope

end

end OAI

-- ---- from OAI.Geometry.Zonotope.EuclideanVolume ----
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma volume_scaled_centered (c : ℝ) (hc : 0 ≤ c) :
    volume ((fun y : ι → ℝ => c • y) '' centered) =
      ENNReal.ofReal (c ^ Fintype.card ι) * ((Fintype.card ι : ℝ≥0∞) + 1) := by
  change volume (c • (centered : Set (ι → ℝ))) = _
  rw [Measure.addHaar_smul_of_nonneg volume hc, Module.finrank_pi, volume_centered]

/-- The coordinate calculation gives actual Euclidean Lebesgue volume. -/
theorem volume_euclidean (c : ℝ) (hc : 0 ≤ c) :
    volume (euclidean c : Set (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (c ^ Fintype.card ι) * ((Fintype.card ι : ℝ≥0∞) + 1) := by
  have hs : (euclidean c : Set (EuclideanSpace ℝ ι)) =
      WithLp.ofLp ⁻¹' ((fun y : ι → ℝ => c • y) '' centered) := by
    ext x
    exact mem_euclidean_iff c x
  rw [hs, (PiLp.volume_preserving_ofLp ι).measure_preimage
    (isCompact_scaled_centered c).measurableSet.nullMeasurableSet,
    volume_scaled_centered c hc]

lemma finAdd_measurePreserving (n m : ℕ) :
    MeasurePreserving (@EuclideanSpace.finAddEquivProd ℝ _ n m) := by
  exact (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m))).comp
      ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℝ)).measurePreserving.comp
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).measurePreserving)

/-- The block product has the product of its two Euclidean volumes. -/
theorem volume_euclideanProduct (n m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    volume (euclideanProduct n m c) =
      (ENNReal.ofReal (c ^ n) * ((n : ℝ≥0∞) + 1)) *
      (ENNReal.ofReal (c ^ m) * ((m : ℝ≥0∞) + 1)) := by
  rw [euclideanProduct, (finAdd_measurePreserving n m).measure_preimage
    ((isCompact_euclidean c).prod (isCompact_euclidean c)).measurableSet.nullMeasurableSet]
  change (volume.prod volume) ((euclidean c : Set (EuclideanSpace ℝ (Fin n))) ×ˢ
    (euclidean c : Set (EuclideanSpace ℝ (Fin m)))) = _
  rw [Measure.prod_prod, volume_euclidean c hc, volume_euclidean c hc]
  simp only [Fintype.card_fin]

/-- Real-valued Euclidean volume for the normalized-ratio calculation. -/
theorem volume_euclidean_toReal (c : ℝ) (hc : 0 ≤ c) :
    (volume (euclidean c : Set (EuclideanSpace ℝ ι))).toReal =
      c ^ Fintype.card ι * ((Fintype.card ι : ℝ) + 1) := by
  rw [volume_euclidean c hc]
  simp [ENNReal.toReal_mul, ENNReal.toReal_add, pow_nonneg hc]

/-- Real-valued volume of the two-block product. -/
theorem volume_euclideanProduct_toReal (n m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (volume (euclideanProduct n m c)).toReal =
      c ^ (n + m) * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
  rw [volume_euclideanProduct n m c hc]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc n),
    ENNReal.toReal_ofReal (pow_nonneg hc m)]
  simp [ENNReal.toReal_add, pow_add]
  ring

end DiagonalZonotope

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.Counterexample ----
namespace OAI

/-!
The geometric projection formulas identify the two actual projection bodies.
Their proved Euclidean volumes are substituted into the normalized ratio before
the final exact arithmetic is performed.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem simplex_twenty_brightness {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume (simplex 20) u =
      (1 / (Nat.factorial 19 : ℝ)) * DiagonalZonotope.support (WithLp.ofLp u) := by
  rw [simplex_projectionVolume (n := 19) (by decide) hu]
  unfold DiagonalZonotope.support
  ring

theorem product_brightness {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume productBody u =
      (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) * blockSupport (n := 10) (m := 10) u := by
  rw [product_projectionVolume hu]
  change (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
      ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|)) /
      (2 * ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) =
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) *
      (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) / 2 +
        ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) / 2)
  ring

theorem simplex_twenty_projectionBody :
    projectionBody (simplex 20) =
      DiagonalZonotope.euclidean (1 / (Nat.factorial 19 : ℝ)) :=
  projectionBody_eq_zonotope (simplex 20) (1 / (Nat.factorial 19 : ℝ))
    (by positivity) (fun _ => simplex_twenty_brightness)

theorem product_projectionBody :
    projectionBody productBody = DiagonalZonotope.euclideanProduct 10 10
      (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) :=
  projectionBody_eq_productZonotope (n := 10) (m := 10) productBody
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10))
    (by positivity) (fun _ => product_brightness)

theorem simplex_twenty_ratio :
    ratio (simplex 20) = ((21 : ℝ) * 20 ^ 20) / (Nat.factorial 20 : ℝ) := by
  unfold ratio bodyVolume
  rw [simplex_twenty_projectionBody,
    DiagonalZonotope.volume_euclidean_toReal _ (by positivity), volume_simplex]
  norm_num [Nat.factorial]

theorem product_ratio_value :
    ratio productBody = (((11 : ℝ) * 10 ^ 10) / (Nat.factorial 10 : ℝ)) ^ 2 := by
  unfold ratio bodyVolume
  rw [product_projectionBody,
    DiagonalZonotope.volume_euclideanProduct_toReal 10 10 _ (by positivity), volume_productBody]
  norm_num [Nat.factorial]

theorem product_to_simplex_ratio :
    ratio productBody / ratio (simplex 20) = (22355476 : ℝ) / 22020096 := by
  rw [product_ratio_value, simplex_twenty_ratio]
  exact numerical_product_ratio

theorem product_exceeds_simplex : ratio (simplex 20) < ratio productBody := by
  have hpos : 0 < ratio (simplex 20) := by
    rw [simplex_twenty_ratio]
    positivity
  have hratio : 1 < ratio productBody / ratio (simplex 20) := by
    rw [product_to_simplex_ratio]
    exact numerical_strict_excess
  simpa using (lt_div_iff₀ hpos).mp hratio

theorem universal_simplex_upper_bound_false :
    ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20)) := by
  intro h
  exact (not_le_of_gt product_exceeds_simplex) (h productBody productBody_convexBody)

end ProjectionCounterexample

end

end OAI

-- ---- mission target ----
open OAI OAI.ProjectionCounterexample
open Set MeasureTheory
open scoped RealInnerProductSpace

theorem solution :
    ¬ (∀ P : Set (E 20), IsConvexBody P → ratio P ≤ ratio (simplex 20)) := by
  first
    | exact OAI.ProjectionCounterexample.universal_simplex_upper_bound_false
    | (apply OAI.ProjectionCounterexample.universal_simplex_upper_bound_false <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.universal_simplex_upper_bound_false <;> assumption)
