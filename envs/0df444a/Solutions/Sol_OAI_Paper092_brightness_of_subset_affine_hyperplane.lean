-- Prove2me | solution 1 for OAI.Paper092.brightness_of_subset_affine_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:47:36.585979+00:00
-- url     : https://prove2.me/submissions/44df20ae-cb37-450d-9503-04ee0a3fa8c5

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProjectionJacobian.lean:L143-L157
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.brightness_of_subset_affine_hyperplane. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
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

-- ---- from OAI.Geometry.ProjectionVolume.Basic ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem normalHyperplane_finrank {n : ℕ} (u : Euclidean n) (hu : u ≠ 0) :
    Module.finrank ℝ (normalHyperplane u) = n - 1 := by
  have h := (Submodule.span ℝ ({u} : Set (Euclidean n))).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton hu, finrank_euclideanSpace_fin] at h
  change Module.finrank ℝ ((Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ) = n - 1
  omega

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.Translation ----
namespace OAI

open Set MeasureTheory
open scoped Pointwise

namespace Paper092

theorem projectionVolume_vadd {n : ℕ} (K : Set (Euclidean n)) (v u : Euclidean n) :
    projectionVolume (v +ᵥ K) u = projectionVolume K u := by
  unfold projectionVolume
  let p := (normalHyperplane u).orthogonalProjectionOnto
  have himage : p '' (v +ᵥ K) = p v +ᵥ (p '' K) := by
    change p '' ((fun x => v + x) '' K) = (fun y => p v + y) '' (p '' K)
    simp only [image_image, map_add]
  rw [himage, measure_vadd]

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.Brightness ----
namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem normalHyperplane_smul {n : ℕ} (u : Euclidean n) {c : ℝ} (hc : c ≠ 0) :
    normalHyperplane (c • u) = normalHyperplane u := by
  unfold normalHyperplane
  rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

theorem projectionVolume_smul {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n)
    {c : ℝ} (hc : c ≠ 0) : projectionVolume K (c • u) = projectionVolume K u := by
  exact congrArg (fun V : Submodule ℝ (Euclidean n) =>
    (volume : Measure V) (V.orthogonalProjectionOnto '' K)) (normalHyperplane_smul u hc)

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProjectionJacobian ----
namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

lemma normal_starProjection_unit {n : ℕ} (u x : Euclidean n) (hu : ‖u‖ = 1) :
    (normalHyperplane u).starProjection x = x - ⟪u, x⟫ • u := by
  simp only [normalHyperplane, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu]

lemma det_one_sub_outer {ι : Type uι} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (1 - Matrix.vecMulVec a a).det = 1 - ∑ i, a i ^ 2 := by
  rw [Matrix.vecMulVec_eq Unit,
    Matrix.det_one_sub_mul_comm, Matrix.det_unique]
  simp [Matrix.replicateRow_mul_replicateCol_apply, dotProduct, pow_two]
theorem hyperplaneProjection_normDet {n : ℕ} (u v : Euclidean n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (hyperplaneProjection u v).normDet = |⟪u, v⟫| := by
  let b := stdOrthonormalBasis ℝ (normalHyperplane v)
  let a := fun i => ⟪u, (b i : Euclidean n)⟫
  have hgram : Matrix.gram ℝ (fun i => hyperplaneProjection u v (b i)) =
      1 - Matrix.vecMulVec a a := by
    ext i j
    change ⟪(normalHyperplane u).starProjection (b i),
      (normalHyperplane u).starProjection (b j)⟫ = _
    rw [normal_starProjection_unit _ _ hu, normal_starProjection_unit _ _ hu]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow, Matrix.sub_apply, Matrix.one_apply,
      Matrix.vecMulVec_apply]
    have hb : ⟪(b i : Euclidean n), (b j : Euclidean n)⟫ = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    rw [hb]
    dsimp [a]
    simp only [real_inner_comm (b i : Euclidean n) u]
    ring
  have hsum : (∑ i, a i ^ 2) = 1 - ⟪u, v⟫ ^ 2 := by
    have h := b.sum_sq_inner_left ((normalHyperplane v).orthogonalProjectionOnto u)
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at h
    change (∑ i, a i ^ 2) = ‖(normalHyperplane v).orthogonalProjectionOnto u‖ ^ 2 at h
    rw [h]
    change ‖(normalHyperplane v).starProjection u‖ ^ 2 = _
    rw [normal_starProjection_unit _ _ hv, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow]
    simp only [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [real_inner_comm v u]
    ring
  have hsq := (hyperplaneProjection u v).normDet_sq_eq_det_gram b
  rw [hgram, det_one_sub_outer, hsum] at hsq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
  have hn := (hyperplaneProjection u v).normDet_nonneg
  have ha := abs_nonneg ⟪u, v⟫
  nlinarith [sq_abs ⟪u, v⟫]

theorem volume_project_hyperplane {n : ℕ} (u v : Euclidean n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (S : Set (normalHyperplane v)) :
    (volume : Measure (normalHyperplane u))
      ((normalHyperplane u).orthogonalProjectionOnto ''
        ((fun x : normalHyperplane v => (x : Euclidean n)) '' S)) =
      ENNReal.ofReal |⟪u, v⟫| * (volume : Measure (normalHyperplane v)) S := by
  let f : normalHyperplane v →ₗ[ℝ] normalHyperplane u :=
    (normalHyperplane u).orthogonalProjectionOnto.toLinearMap.comp
      (normalHyperplane v).subtype
  have hf : f.normDet = (hyperplaneProjection u v).normDet := by
    have hp : ∀ x, hyperplaneProjection u v x ∈ normalHyperplane u := by
      intro x
      exact ((normalHyperplane u).orthogonalProjectionOnto (x : Euclidean n)).property
    have he : f = (hyperplaneProjection u v).codRestrict (normalHyperplane u) hp := by
      ext x
      rfl
    rw [he]
    exact LinearMap.normDet_codRestrict hp
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hrank : Module.finrank ℝ (normalHyperplane v) =
      Module.finrank ℝ (normalHyperplane u) := by
    rw [normalHyperplane_finrank v hv0, normalHyperplane_finrank u hu0]
  have h := f.euclideanHausdorffMeasure_image_eq_normDet_mul_volume S
  rw [hrank, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    hf, hyperplaneProjection_normDet u v hu hv] at h
  have himage : f '' S = (normalHyperplane u).orthogonalProjectionOnto ''
      ((fun x : normalHyperplane v => (x : Euclidean n)) '' S) := by
    rw [Set.image_image]
    rfl
  rw [himage] at h
  exact h

theorem projectionVolume_of_subset_affine_hyperplane {n : ℕ} (u v : Euclidean n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (c : ℝ) (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, ⟪v, x⟫ = c) :
    projectionVolume S u = ENNReal.ofReal |⟪u, v⟫| * μHE[n - 1] S := by
  let T : Set (Euclidean n) := ((-c) • v) +ᵥ S
  have hT : T ⊆ (normalHyperplane v : Set (Euclidean n)) := by
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪v, (-c) • v + y⟫ = 0
    simp [inner_add_right, inner_smul_right, hv, hS y hy]
  let Q : Set (normalHyperplane v) := {x | (x : Euclidean n) ∈ T}
  have hQ : (fun x : normalHyperplane v => (x : Euclidean n)) '' Q = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hT hx⟩, hx, rfl⟩
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hQV : (volume : Measure (normalHyperplane v)) Q = μHE[n - 1] S := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      normalHyperplane_finrank v hv0]
    have h := (isometry_subtype_coe : Isometry
      (fun x : normalHyperplane v => (x : Euclidean n))).euclideanHausdorffMeasure_image
      (d := n - 1) Q
    have hQ' : (Subtype.val : normalHyperplane v → Euclidean n) '' Q = T := hQ
    calc
      (μHE[n - 1] : Measure (normalHyperplane v)) Q =
          (μHE[n - 1] : Measure (Euclidean n)) (Subtype.val '' Q) := h.symm
      _ = (μHE[n - 1] : Measure (Euclidean n)) T :=
        congrArg (fun A : Set (Euclidean n) => (μHE[n - 1] : Measure (Euclidean n)) A) hQ'
      _ = (μHE[n - 1] : Measure (Euclidean n)) S :=
        measure_vadd (μHE[n - 1] : Measure (Euclidean n)) ((-c) • v) S
  have h := volume_project_hyperplane u v hu hv Q
  rw [hQ, hQV] at h
  change projectionVolume T u = _ at h
  simpa only [T, projectionVolume_vadd] using h

theorem brightness_of_subset_affine_hyperplane {n : ℕ} (u v : Euclidean n)
    (hv : ‖v‖ = 1) (c : ℝ) (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, ⟪v, x⟫ = c) :
    brightness S u = |⟪u, v⟫| * (μHE[n - 1] S).toReal := by
  by_cases hu : u = 0
  · simp [hu, brightness]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hunit : ‖‖u‖⁻¹ • u‖ = 1 := by
    simp [norm_smul, hn.ne']
  have h := projectionVolume_of_subset_affine_hyperplane
    (‖u‖⁻¹ • u) v hunit hv c S hS
  rw [projectionVolume_smul S u (inv_ne_zero hn.ne')] at h
  rw [brightness, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  simp only [real_inner_smul_left, abs_mul, abs_inv, abs_of_pos hn]
  field_simp

end Paper092

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
universe uι
open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

theorem solution {n : ℕ} (u v : Euclidean n)
    (hv : ‖v‖ = 1) (c : ℝ) (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, ⟪v, x⟫ = c) :
    brightness S u = |⟪u, v⟫| * (μHE[n - 1] S).toReal := by
  first
    | exact OAI.Paper092.brightness_of_subset_affine_hyperplane u v hv c S hS
    | exact OAI.Paper092.brightness_of_subset_affine_hyperplane
    | (apply OAI.Paper092.brightness_of_subset_affine_hyperplane <;> assumption)
    | (intros; apply OAI.Paper092.brightness_of_subset_affine_hyperplane <;> assumption)
