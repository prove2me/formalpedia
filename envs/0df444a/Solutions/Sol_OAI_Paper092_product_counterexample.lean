-- Prove2me | solution 1 for OAI.Paper092.product_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:59:59.390001+00:00
-- url     : https://prove2.me/submissions/64d38359-ee15-4499-87aa-2b36a30eb8e4

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductCounterexample.lean:L31-L58
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Paper092.product_counterexample.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Paper092_product_counterexample) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
import Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_Extrusion
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexZonotope
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductZonotope
import Theorems.Thm_OAI_Paper092_cube_add_diagonal_eq_union
import Theorems.Thm_OAI_Paper092_productWitness_brightness
import Theorems.Thm_OAI_Paper092_simplexZonotope_support
import Theorems.Thm_OAI_Paper092_standardSimplex_volume

-- ---- from OAI.Geometry.ProjectionVolume.Arithmetic ----
namespace OAI

namespace Paper092

theorem dimension_twenty_ratio :
    simplexConstant 10 * simplexConstant 10 / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 := by
  norm_num [simplexConstant, Nat.factorial]

theorem dimension_twenty_strict :
    simplexConstant 20 < simplexConstant 10 * simplexConstant 10 := by
  norm_num [simplexConstant, Nat.factorial]

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.SimplexGeometry ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

theorem standardSimplex_isCompact (n : ℕ) : IsCompact (standardSimplex n) :=
  ((Set.finite_range _).insert 0).isCompact_convexHull ℝ

theorem standardSimplex_convex (n : ℕ) : Convex ℝ (standardSimplex n) :=
  convex_convexHull ℝ _

theorem standardSimplex_interior_nonempty (n : ℕ) :
    (interior (standardSimplex n)).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  have hspan : Submodule.span ℝ
      (range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
    have hfun : (fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) =
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by
      funext i
      simp
    rw [hfun]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
  apply SetLike.coe_injective
  rw [affineSpan_insert_zero, hspan]
  rfl

theorem productWitness_eq_preimage :
    productWitness = splitBlocks ⁻¹' (standardSimplex 10 ×ˢ standardSimplex 10) := rfl

theorem productWitness_isCompact : IsCompact productWitness := by
  rw [productWitness_eq_preimage]
  exact splitBlocks.toHomeomorph.isCompact_preimage.mpr
    ((standardSimplex_isCompact 10).prod (standardSimplex_isCompact 10))

theorem productWitness_convex : Convex ℝ productWitness := by
  rw [productWitness_eq_preimage]
  exact ((standardSimplex_convex 10).prod (standardSimplex_convex 10)).linear_preimage
    splitBlocks.toLinearMap

theorem productWitness_interior_nonempty : (interior productWitness).Nonempty := by
  rw [productWitness_eq_preimage]
  change (interior (splitBlocks.toHomeomorph ⁻¹'
    (standardSimplex 10 ×ˢ standardSimplex 10))).Nonempty
  rw [← splitBlocks.toHomeomorph.preimage_interior, interior_prod_eq]
  exact ((standardSimplex_interior_nonempty 10).prod
    (standardSimplex_interior_nonempty 10)).preimage splitBlocks.surjective

theorem productWitness_is_convex_body :
    IsCompact productWitness ∧ Convex ℝ productWitness ∧ (interior productWitness).Nonempty :=
  ⟨productWitness_isCompact, productWitness_convex, productWitness_interior_nonempty⟩

theorem productWitness_volume_pos : 0 < (volume productWitness).toReal :=
  ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_nonempty_interior volume
    productWitness_interior_nonempty)) productWitness_isCompact.measure_lt_top.ne

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductVolume ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Paper092

theorem splitBlocks_measurePreserving : MeasurePreserving splitBlocks volume volume := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin 20)
  have h₂ := (volume_measurePreserving_piCongrLeft (fun _ : Fin 20 => ℝ)
    (finSumFinEquiv : Fin 10 ⊕ Fin 10 ≃ Fin 20)).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin 10 ⊕ Fin 10 => ℝ)
  have h₄ := (PiLp.volume_preserving_toLp (Fin 10)).prod
    (PiLp.volume_preserving_toLp (Fin 10))
  convert h₄.comp (h₃.comp (h₂.comp h₁)) using 1
  all_goals rfl

theorem productWitness_volume_product :
    volume productWitness = volume (standardSimplex 10) * volume (standardSimplex 10) := by
  rw [productWitness_eq_preimage,
    splitBlocks_measurePreserving.measure_preimage
      (((standardSimplex_isCompact 10).prod (standardSimplex_isCompact 10)).measurableSet.nullMeasurableSet)]
  exact Measure.prod_prod _ _

theorem productWitness_volume :
    volume productWitness = ENNReal.ofReal ((1 / (Nat.factorial 10 : ℝ)) ^ 2) := by
  rw [productWitness_volume_product, standardSimplex_volume,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem productWitness_volume_real :
    (volume productWitness).toReal = (1 / (Nat.factorial 10 : ℝ)) ^ 2 := by
  rw [productWitness_volume, ENNReal.toReal_ofReal (by positivity)]

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.SupportGeometry ----
namespace OAI

universe uE uF uι uH

open Set
open scoped Pointwise

namespace Paper092.SupportGeometry

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem le_support {K : Set E} (hK : IsCompact K) (f : E →L[ℝ] ℝ)
    {x : E} (hx : x ∈ K) : f x ≤ support K f :=
  le_csSup (hK.image f.continuous).bddAbove (mem_image_of_mem f hx)

theorem support_le {K : Set E} (hK : K.Nonempty) (f : E →L[ℝ] ℝ)
    {a : ℝ} (ha : ∀ x ∈ K, f x ≤ a) : support K f ≤ a :=
  csSup_le (hK.image f) (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)

theorem support_smul (K : Set E) (f : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) :
    support (c • K) f = c * support K f := by
  unfold support
  rw [image_smul_comm f c K (fun x => f.map_smul c x), Real.sSup_smul_of_nonneg hc]
  rfl

theorem support_prod {A : Set E} {B : Set F} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) (g : F →L[ℝ] ℝ) :
    support (A ×ˢ B) (f.coprod g) = support A f + support B g := by
  unfold support
  have himage : f.coprod g '' (A ×ˢ B) = f '' A + g '' B := by
    change (fun x : E × F => f x.1 + g x.2) '' (A ×ˢ B) = _
    rw [image_prod (fun x y => f x + g y), ← image2_add,
      image2_image_left, image2_image_right]
  rw [himage]
  exact csSup_add (hneA.image f) (hA.image f.continuous).bddAbove
    (hneB.image g) (hB.image g.continuous).bddAbove

theorem mem_iff_le_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : E} :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  refine ⟨fun hx f => le_support hK f hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hx
  exact (hux.trans_le ((h f).trans (support_le hne f fun y hy => (hu y hy).le))).false

theorem isCompact_segment (x y : E) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

section InnerProduct

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem mem_iff_inner_le_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : H} :
    x ∈ K ↔ ∀ u : H, inner ℝ u x ≤ support K (innerSL ℝ u) := by
  rw [mem_iff_le_support hK hne hconv]
  constructor
  · intro h u
    exact h (innerSL ℝ u)
  · intro h f
    obtain ⟨u, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective f
    exact h u

theorem halfSpaces_eq_of_eq_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) (p : H → ℝ) (hp : ∀ u, p u = support K (innerSL ℝ u)) :
    {x | ∀ u : H, inner ℝ u x ≤ p u} = K := by
  ext x
  simp_rw [mem_ofPred_eq, hp]
  exact (mem_iff_inner_le_support hK hne hconv).symm

end InnerProduct

end Paper092.SupportGeometry

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.Extrusion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Paper092

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem det_shearMatrix (i : ι) : (shearMatrix i).det = 1 := by
  simpa [shearMatrix, Matrix.one_apply] using
    Matrix.det_updateCol_sum (1 : Matrix ι ι ℝ) i (fun _ => (1 : ℝ))

omit [Fintype ι] in
theorem cellMap_mem_iff (i : ι) (x : ι → ℝ) :
    cellMap i x ∈ extrusionCell i ↔ x ∈ unitCube ι := by
  simp only [extrusionCell, cellMap, unitCube, mem_ofPred_eq, mem_Icc, Pi.le_def,
    Pi.zero_apply, Pi.one_apply, ite_true]
  constructor
  · rintro ⟨hi, h⟩
    constructor <;> intro j
    · by_cases hj : j = i
      · subst j; linarith
      · have := h j hj
        simp only [ite_eq_right hj] at this
        linarith
    · by_cases hj : j = i
      · subst j; linarith
      · have := h j hj
        simp only [ite_eq_right hj] at this
        linarith
  · rintro ⟨h0, h1⟩
    refine ⟨⟨by linarith [h0 i], by linarith [h1 i]⟩, ?_⟩
    intro j hj
    simp only [ite_eq_right hj]
    constructor <;> linarith [h0 j, h1 j]

theorem cellMap_eq_matrix (i : ι) (x : ι → ℝ) :
    cellMap i x = Pi.single i 1 + Matrix.toLin' (shearMatrix i) x := by
  funext j
  simp only [cellMap, Pi.add_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    shearMatrix, Matrix.updateCol_apply, Matrix.one_apply]
  by_cases hj : j = i
  · subst j
    have hsum : ∀ k : ι,
        (if k = i then 1 else if i = k then 1 else 0) * x k =
          if k = i then x k else 0 := by
      intro k
      by_cases hk : k = i
      · subst k; simp
      · simp [hk, Ne.symm hk]
    simp_rw [hsum]
    simp
  · have hsum : ∀ k : ι,
        (if k = i then 1 else if j = k then 1 else 0) * x k =
          (if k = i then x i else 0) + (if k = j then x j else 0) := by
      intro k
      by_cases hki : k = i
      · subst k; simp [Ne.symm hj]
      · by_cases hkj : k = j
        · subst k; simp [hj]
        · simp [hki, hkj, Ne.symm hkj]
    simp_rw [hsum]
    simp [hj, Finset.sum_add_distrib]

theorem cellMap_measurePreserving (i : ι) :
    MeasurePreserving (cellMap i) volume volume := by
  have hs : MeasurePreserving (Matrix.toLin' (shearMatrix i)) volume volume := by
    refine ⟨(Matrix.toLin' (shearMatrix i)).continuous_of_finiteDimensional.measurable, ?_⟩
    simpa [det_shearMatrix] using
      Real.map_matrix_volume_pi_eq_smul_volume_pi
        (M := shearMatrix i) (by rw [det_shearMatrix]; norm_num)
  have h := (measurePreserving_add_left (volume : Measure (ι → ℝ)) (Pi.single i 1)).comp hs
  simpa only [Function.comp_def, ← cellMap_eq_matrix] using h

omit [DecidableEq ι] in
theorem extrusionCell_measurable (i : ι) : MeasurableSet (extrusionCell i) := by
  simp only [extrusionCell, ofPred_and, ofPred_forall]
  exact ((measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (measurable_pi_apply i) measurable_const)).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_le ((measurable_pi_apply i).sub measurable_const)
        (measurable_pi_apply j)).inter
      (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)))

omit [DecidableEq ι] in
theorem unitCube_volume : volume (unitCube ι) = 1 := by
  simp [unitCube, Real.volume_Icc_pi]

theorem extrusionCell_volume (i : ι) : volume (extrusionCell i) = 1 := by
  have hpre : cellMap i ⁻¹' extrusionCell i = unitCube ι :=
    Set.ext (cellMap_mem_iff i)
  rw [← (cellMap_measurePreserving i).measure_preimage
    (extrusionCell_measurable i).nullMeasurableSet, hpre, unitCube_volume]

omit [DecidableEq ι] in
theorem coordinate_eq_null (i : ι) (c : ℝ) :
    volume {x : ι → ℝ | x i = c} = 0 := by
  simpa [volume_pi] using Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i c

theorem coordinates_eq_null (i j : ι) (hij : i ≠ j) :
    volume {x : ι → ℝ | x i = x j} = 0 := by
  let f : (ι → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h
    have hz : f (Pi.single i 1) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [h]
      exact Submodule.mem_top
    simp [f, Ne.symm hij] at hz
  have hset : {x : ι → ℝ | x i = x j} = (LinearMap.ker f : Set (ι → ℝ)) := by
    ext x
    change x i = x j ↔ x i - x j = 0
    exact sub_eq_zero.symm
  rw [hset]
  exact Measure.addHaar_submodule (volume : Measure (ι → ℝ)) (LinearMap.ker f) hker

omit [DecidableEq ι] in
theorem cube_cell_aedisjoint (i : ι) :
    AEDisjoint volume (unitCube ι) (extrusionCell i) := by
  apply measure_mono_null _ (coordinate_eq_null i 1)
  rintro x ⟨hx, hi⟩
  exact le_antisymm (hx.2 i) hi.1.1

theorem cells_aedisjoint : Pairwise (fun i j : ι =>
    AEDisjoint volume (extrusionCell i) (extrusionCell j)) := by
  intro i j hij
  apply measure_mono_null _ (coordinates_eq_null i j hij)
  rintro x ⟨hi, hj⟩
  exact le_antisymm (hj.2 i hij).2 (hi.2 j hij.symm).2

theorem volume_cube_add_diagonal [Nonempty ι] :
    volume (unitCube ι + segment ℝ (0 : ι → ℝ) 1) = Fintype.card ι + 1 := by
  rw [cube_add_diagonal_eq_union,
    measure_union₀ ((MeasurableSet.iUnion extrusionCell_measurable).nullMeasurableSet)
      (AEDisjoint.iUnion_right_iff.mpr cube_cell_aedisjoint),
    measure_iUnion₀ cells_aedisjoint (fun i => (extrusionCell_measurable i).nullMeasurableSet),
    unitCube_volume]
  simp [extrusionCell_volume, add_comm]

theorem volume_Icc_add_segment_one (d : ℕ) (hd : 0 < d) :
    volume (Icc (0 : Fin d → ℝ) 1 + segment ℝ (0 : Fin d → ℝ) 1) = d + 1 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simpa [unitCube] using (volume_cube_add_diagonal (ι := Fin d))

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.EuclideanVolume ----
namespace OAI

universe uι

open Set MeasureTheory
open scoped Pointwise

namespace Paper092

theorem volume_euclidean_image {ι : Type uι} [Fintype ι] (s : Set (ι → ℝ)) :
    (volume : Measure (EuclideanSpace ℝ ι)) (WithLp.toLp 2 '' s) = volume s := by
  change volume ((MeasurableEquiv.toLp 2 (ι → ℝ)) '' s) = volume s
  rw [MeasurableEquiv.image_eq_preimage_symm]
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).measure_preimage_equiv s

theorem toLp_image_add_segment {ι : Type uι} [Fintype ι] (s : Set (ι → ℝ)) :
    WithLp.toLp 2 '' (s + segment ℝ (0 : ι → ℝ) 1) =
      WithLp.toLp 2 '' s + segment ℝ (0 : EuclideanSpace ℝ ι)
        (WithLp.toLp 2 (1 : ι → ℝ)) := by
  let e := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  have ha := Set.image_add (s := s) (t := segment ℝ (0 : ι → ℝ) 1) e.toAddEquiv
  have hs := image_segment ℝ e.toAffineEquiv.toAffineMap (0 : ι → ℝ) 1
  simpa [e] using ha.trans (congrArg (fun t => e '' s + t) hs)

theorem volume_euclidean_cube_add_diagonal (d : ℕ) (hd : 0 < d) :
    volume ((WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1) +
      segment ℝ (0 : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 (1 : Fin d → ℝ))) =
        d + 1 := by
  rw [← toLp_image_add_segment, volume_euclidean_image]
  exact volume_Icc_add_segment_one d hd

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.SimplexZonotope ----
namespace OAI

universe uE uι

open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

theorem simplexZonotope_isCompact (d : ℕ) : IsCompact (simplexZonotope d) := by
  unfold simplexZonotope
  exact (Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
    isCompact_singleton (fun _ _ => SupportGeometry.isCompact_segment _ _)).add
      (SupportGeometry.isCompact_segment _ _)

theorem simplexZonotope_nonempty (d : ℕ) : (simplexZonotope d).Nonempty := by
  unfold simplexZonotope
  exact (Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
    (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)).add
      ⟨_, left_mem_segment ℝ _ _⟩

theorem simplexZonotope_convex (d : ℕ) : Convex ℝ (simplexZonotope d) := by
  unfold simplexZonotope
  exact (convex_sum _ (fun _ _ => convex_segment _ _)).add (convex_segment _ _)

theorem centered_segment_eq_vadd {E : Type uE} [AddCommGroup E] [Module ℝ E] (v : E) :
    segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v) =
      (-(1 / 2 : ℝ) • v) +ᵥ segment ℝ 0 v := by
  rw [vadd_segment]
  simp only [vadd_eq_add, add_zero]
  congr 1
  symm
  simpa only [add_smul, one_smul] using
    congrArg (fun a : ℝ => a • v) (by norm_num : -(1 / 2 : ℝ) + 1 = 1 / 2)

theorem sum_centered_segments_eq_vadd {ι : Type uι} {E : Type uE} [Fintype ι] [AddCommGroup E]
    [Module ℝ E] (v : ι → E) :
    (∑ i, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i)) =
      (-(1 / 2 : ℝ) • ∑ i, v i) +ᵥ parallelepiped v := by
  simp_rw [centered_segment_eq_vadd, ← image_vadd, vadd_eq_add, ← singleton_add]
  rw [Finset.sum_add_distrib, Set.finsetSum_singleton, ← Finset.smul_sum,
    ← parallelepiped_eq_sum_segment]

theorem coordinate_segments_eq_cube (d : ℕ) :
    (∑ i : Fin d, segment ℝ (0 : Euclidean d) (EuclideanSpace.single i (1 : ℝ))) =
      WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1 := by
  rw [← parallelepiped_eq_sum_segment, parallelepiped]
  congr 1
  funext t
  ext j
  simp [WithLp.ofLp_sum, Pi.single_apply]

theorem smul_segment_image {E : Type uE} [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (x y : E) : r • segment ℝ x y = segment ℝ (r • x) (r • y) :=
  image_segment ℝ (r • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap x y

theorem simplexZonotope_eq_vadd_smul (d : ℕ) :
    simplexZonotope d =
      -(((d - 1).factorial : ℝ)⁻¹ • WithLp.toLp 2 (1 : Fin d → ℝ)) +ᵥ
      (((d - 1).factorial : ℝ)⁻¹ •
        ((WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1) +
          segment ℝ (0 : Euclidean d) (WithLp.toLp 2 (1 : Fin d → ℝ)))) := by
  let r : ℝ := ((d - 1).factorial : ℝ)⁻¹
  let w : Euclidean d := WithLp.toLp 2 (1 : Fin d → ℝ)
  have hsum : (∑ i : Fin d, EuclideanSpace.single i (1 : ℝ)) = w := by
    ext j
    simp [w, WithLp.ofLp_sum, Pi.single_apply]
  have hpara : parallelepiped (fun i : Fin d => r • EuclideanSpace.single i (1 : ℝ)) =
      r • (WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1) := by
    rw [parallelepiped_eq_sum_segment, ← coordinate_segments_eq_cube,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_segment_image, smul_zero]
  change (∑ i : Fin d, segment ℝ (-(1 / 2 : ℝ) • (r • EuclideanSpace.single i (1 : ℝ)))
      ((1 / 2 : ℝ) • (r • EuclideanSpace.single i (1 : ℝ)))) +
      segment ℝ (-(1 / 2 : ℝ) • (r • w)) ((1 / 2 : ℝ) • (r • w)) = _
  rw [sum_centered_segments_eq_vadd, ← Finset.smul_sum, hsum,
    centered_segment_eq_vadd, hpara]
  have hseg : segment ℝ (0 : Euclidean d) (r • w) = r • segment ℝ 0 w := by
    rw [smul_segment_image, smul_zero]
  rw [hseg]
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  rw [add_add_add_comm, singleton_add_singleton,
    ← smul_add r (WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1)
      (segment ℝ (0 : Euclidean d) w)]
  congr 2
  calc
    -(1 / 2 : ℝ) • (r • w) + -(1 / 2 : ℝ) • (r • w) =
        (-1 : ℝ) • (r • w) := by rw [← add_smul]; norm_num
    _ = -(r • w) := neg_one_smul ℝ _

theorem volume_simplexZonotope (d : ℕ) (hd : 0 < d) :
    volume (simplexZonotope d) =
      ENNReal.ofReal (((d : ℝ) + 1) / (((d - 1).factorial : ℝ) ^ d)) := by
  have hfac : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  rw [simplexZonotope_eq_vadd_smul, measure_vadd, Measure.addHaar_smul,
    finrank_euclideanSpace_fin, volume_euclidean_cube_add_diagonal d hd]
  rw [abs_pow, abs_inv, abs_of_pos hfac]
  rw [ENNReal.ofReal_div_of_pos (pow_pos hfac d)]
  simp [inv_pow, div_eq_mul_inv, mul_comm,
    ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one,
    ENNReal.ofReal_pow hfac.le, ENNReal.ofReal_inv_of_pos (pow_pos hfac d)]

theorem simplexZonotope_volume (d : ℕ) (hd : 0 < d) :
    (volume (simplexZonotope d)).toReal =
      ((d : ℝ) + 1) / (((d - 1).factorial : ℝ) ^ d) := by
  rw [volume_simplexZonotope d hd, ENNReal.toReal_ofReal]
  positivity

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductZonotope ----
namespace OAI

universe uE uF

open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

theorem productZonotope_isCompact : IsCompact productZonotope := by
  unfold productZonotope
  have h : IsCompact ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    IsCompact.smul _ (simplexZonotope_isCompact 10)
  exact splitBlocks.toHomeomorph.isCompact_preimage.mpr (h.prod h)

theorem productZonotope_nonempty : productZonotope.Nonempty := by
  unfold productZonotope
  have h : ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10).Nonempty :=
    (simplexZonotope_nonempty 10).smul_set
  exact (h.prod h).preimage splitBlocks.surjective

theorem productZonotope_convex : Convex ℝ productZonotope := by
  unfold productZonotope
  have h : Convex ℝ ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    (simplexZonotope_convex 10).smul _
  exact (h.prod h).linear_preimage splitBlocks.toLinearMap

theorem inner_splitBlocks_sum (u v : Euclidean 20) :
    inner ℝ u v = inner ℝ (firstBlock u) (firstBlock v) +
      inner ℝ (secondBlock u) (secondBlock v) := by
  exact Fin.sum_univ_add (fun i : Fin (10 + 10) => inner ℝ (u i) (v i))

theorem support_preimage_equiv {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (K : Set F)
    (f : F →L[ℝ] ℝ) :
    SupportGeometry.support (e ⁻¹' K) (f.comp e.toContinuousLinearMap) =
      SupportGeometry.support K f := by
  unfold SupportGeometry.support
  change sSup ((f ∘ e) '' (e ⁻¹' K)) = _
  rw [image_comp f e, image_preimage_eq K e.surjective]

theorem productZonotope_support_factor (u : Euclidean 20) :
    SupportGeometry.support productZonotope (innerSL ℝ u) =
      (1 / (Nat.factorial 10 : ℝ)) *
        (SupportGeometry.support (simplexZonotope 10) (innerSL ℝ (firstBlock u)) +
          SupportGeometry.support (simplexZonotope 10) (innerSL ℝ (secondBlock u))) := by
  have hlin : innerSL ℝ u =
      ((innerSL ℝ (firstBlock u)).coprod (innerSL ℝ (secondBlock u))).comp
        splitBlocks.toContinuousLinearMap := by
    ext y
    exact inner_splitBlocks_sum u y
  have hc : IsCompact ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    IsCompact.smul _ (simplexZonotope_isCompact 10)
  have hn : ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10).Nonempty :=
    (simplexZonotope_nonempty 10).smul_set
  rw [hlin, productZonotope, support_preimage_equiv,
    SupportGeometry.support_prod hc hn hc hn,
    SupportGeometry.support_smul _ _ (by positivity),
    SupportGeometry.support_smul _ _ (by positivity), mul_add]

theorem productZonotope_support (u : Euclidean 20) :
    SupportGeometry.support productZonotope (innerSL ℝ u) =
      ((∑ i : Fin 10, |firstBlock u i|) + |∑ i : Fin 10, firstBlock u i| +
        (∑ i : Fin 10, |secondBlock u i|) + |∑ i : Fin 10, secondBlock u i|) /
          (2 * (Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
  rw [productZonotope_support_factor, simplexZonotope_support, simplexZonotope_support]
  change (1 / (Nat.factorial 10 : ℝ)) *
    (((∑ i : Fin 10, |firstBlock u i|) + |∑ i : Fin 10, firstBlock u i|) /
        (2 * (Nat.factorial 9 : ℝ)) +
      ((∑ i : Fin 10, |secondBlock u i|) + |∑ i : Fin 10, secondBlock u i|) /
        (2 * (Nat.factorial 9 : ℝ))) = _
  ring

theorem productZonotope_volume_product :
    volume productZonotope =
      volume ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) *
      volume ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) := by
  have hc : IsCompact ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    IsCompact.smul _ (simplexZonotope_isCompact 10)
  rw [productZonotope, splitBlocks_measurePreserving.measure_preimage
    (hc.prod hc).measurableSet.nullMeasurableSet]
  exact Measure.prod_prod _ _

theorem productZonotope_volume_real :
    (volume productZonotope).toReal =
      (121 : ℝ) / ((Nat.factorial 9 : ℝ) ^ 20 * (Nat.factorial 10 : ℝ) ^ 20) := by
  have hscaled :
      (volume ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10)).toReal =
        (1 / (Nat.factorial 10 : ℝ)) ^ 10 * (11 / (Nat.factorial 9 : ℝ) ^ 10) := by
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_pow, abs_of_nonneg (by positivity),
      simplexZonotope_volume 10 (by norm_num)]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
  rw [productZonotope_volume_product, ENNReal.toReal_mul, hscaled]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProjectionReconstruction ----
namespace OAI

namespace Paper092

theorem projectionBody_eq_of_brightness_eq_support {n : ℕ}
    {K C : Set (Euclidean n)} (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C)
    (h : ∀ u, brightness K u = SupportGeometry.support C (innerSL ℝ u)) :
    projectionBody K = C :=
  SupportGeometry.halfSpaces_eq_of_eq_support hC hne hconv (brightness K) h

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductCounterexample ----
namespace OAI

open MeasureTheory

namespace Paper092

theorem productWitness_projectionBody :
    projectionBody productWitness = productZonotope := by
  apply projectionBody_eq_of_brightness_eq_support productZonotope_isCompact
    productZonotope_nonempty productZonotope_convex
  intro u
  rw [productWitness_brightness, productZonotope_support]

theorem productZonotope_normalized_volume :
    (volume productZonotope).toReal / (volume productWitness).toReal ^ 19 =
      simplexConstant 10 * simplexConstant 10 := by
  rw [productZonotope_volume_real, productWitness_volume_real]
  norm_num [simplexConstant, Nat.factorial]

theorem productWitness_normalizedProjectionVolume :
    normalizedProjectionVolume productWitness = simplexConstant 10 * simplexConstant 10 := by
  unfold normalizedProjectionVolume
  rw [productWitness_projectionBody]
  exact productZonotope_normalized_volume

theorem product_counterexample :
    (IsCompact productWitness ∧ Convex ℝ productWitness ∧
      (interior productWitness).Nonempty) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 ∧
    1 < normalizedProjectionVolume productWitness / simplexConstant 20 ∧
    (volume (projectionBody productWitness)).toReal >
      simplexConstant 20 * (volume productWitness).toReal ^ 19 := by
  have hratio : normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 := by
    rw [productWitness_normalizedProjectionVolume]
    exact dimension_twenty_ratio
  have hchoose : normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) := by
    rw [hratio, Nat.choose_eq_factorial_div_factorial (by norm_num : 10 ≤ 20)]
    norm_num [Nat.factorial]
  have hgt : 1 < normalizedProjectionVolume productWitness / simplexConstant 20 := by
    rw [hratio]
    norm_num
  have hnorm : simplexConstant 20 < normalizedProjectionVolume productWitness := by
    rw [productWitness_normalizedProjectionVolume]
    exact dimension_twenty_strict
  change simplexConstant 20 <
    (volume (projectionBody productWitness)).toReal / (volume productWitness).toReal ^ 19 at hnorm
  have hvol := (lt_div_iff₀ (pow_pos productWitness_volume_pos 19)).mp hnorm
  exact ⟨productWitness_is_convex_body, hchoose, hratio, hgt, hvol⟩

end Paper092

end OAI

-- ---- mission target ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise
open MeasureTheory

theorem solution :
    (IsCompact productWitness ∧ Convex ℝ productWitness ∧
      (interior productWitness).Nonempty) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 ∧
    1 < normalizedProjectionVolume productWitness / simplexConstant 20 ∧
    (volume (projectionBody productWitness)).toReal >
      simplexConstant 20 * (volume productWitness).toReal ^ 19 := by
  first
    | exact OAI.Paper092.product_counterexample
    | (apply OAI.Paper092.product_counterexample <;> assumption)
    | (intros; apply OAI.Paper092.product_counterexample <;> assumption)
