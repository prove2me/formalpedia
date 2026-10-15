-- Prove2me | solution 1 for OAI.RuledApproximation.framed_local_cover_of_shape
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:13:36.445315+00:00
-- url     : https://prove2.me/submissions/0cb02306-f43f-4c18-820e-d964ffa9b630

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SquareCover.lean:L12-L83
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.framed_local_cover_of_shape. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Theorems.Thm_OAI_RuledApproximation_frame_integral_image
import Theorems.Thm_OAI_RuledApproximation_local_finite_certificate
import Theorems.Thm_OAI_RuledApproximation_projectedCylinder_mem_iff

-- ---- from OAI.Geometry.RuledCovering.Projection ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma physicalDirection_norm_sq (h : ℝ) (g : Plane) :
    ‖physicalDirection h g‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 := by
  rw [physicalDirection, norm_vec3_sq]
  ring

lemma inner_rawProjection (h : ℝ) (g p q : Plane) :
    inner ℝ (rawProjection h g p) (rawProjection h g q) =
      inner ℝ (planeEmbedding h p) (planeEmbedding h q) -
      inner ℝ (physicalDirection h g) (planeEmbedding h p) *
        inner ℝ (physicalDirection h g) (planeEmbedding h q) /
          ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (planeEmbedding h p) (physicalDirection h g)]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

lemma rawProjection_normDet_sq (h : ℝ) (g : Plane) :
    (rawProjection h g).normDet ^ 2 = h ^ 2 / ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  have hd := (rawProjection h g).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
  rw [hd, Matrix.det_fin_two]
  simp only [Matrix.gram_apply, inner_rawProjection, EuclideanSpace.basisFun_apply,
    planeEmbedding_apply, physicalDirection, inner_vec3,
    PiLp.single_apply, Fin.isValue, ↓reduceIte, mul_zero, mul_one,
    one_mul, zero_add]
  simp only [Fin.reduceEq, ↓reduceIte]
  rw [show ‖vec3 1 (g 0) (h * g 1)‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 by
    rw [norm_vec3_sq]; ring]
  have hden : 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma rawProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (rawProjection h g).normDet = h / ‖physicalDirection h g‖ := by
  have hn := physicalDirection_norm_pos h g
  have hs : ((rawProjection h g).normDet * ‖physicalDirection h g‖) ^ 2 = h ^ 2 := by
    rw [mul_pow, rawProjection_normDet_sq, div_mul_cancel₀ _ (pow_ne_zero 2 hn.ne')]
  have hnon := mul_nonneg (rawProjection h g).normDet_nonneg hn.le
  apply (eq_div_iff hn.ne').mpr
  nlinarith

lemma physicalWeight_eq_inv_norm (h : ℝ) (g : Plane) :
    physicalWeight h g = 1 / ‖physicalDirection h g‖ := by
  rw [physicalWeight, ← physicalDirection_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]

lemma perpendicularProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (perpendicularProjection h g).normDet = h * physicalWeight h g := by
  rw [perpendicularProjection, LinearMap.normDet_codRestrict, rawProjection_normDet hh,
    physicalWeight_eq_inv_norm]
  ring

lemma perpendicularPlane_finrank (u : Space) (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((Submodule.span ℝ ({u} : Set Space))ᗮ) = 2 := by
  have hne : u ≠ 0 := by intro hz; simp [hz] at hu
  have hd := (Submodule.span ℝ ({u} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  omega

lemma perpendicularProjection_volume {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    volume.real (perpendicularProjection h g '' P) =
      h * physicalWeight h g * volume.real P := by
  have hf := (perpendicularProjection h g).euclideanHausdorffMeasure_image_eq_normDet_mul_volume P
  have hm : (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ Plane) : Measure ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ)) = volume := by
    convert InnerProductSpace.euclideanHausdorffMeasure_eq_volume using 1
    simp only [finrank_euclideanSpace_fin, perpendicularPlane_finrank _ (physicalUnit_norm h g)]
  rw [hm] at hf
  rw [measureReal_def, hf, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (perpendicularProjection h g).normDet_nonneg,
    perpendicularProjection_normDet hh]
  rfl

lemma projectedCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).area = h * volume.real P * physicalWeight h g := by
  rw [Cylinder.area, projectedCylinder, perpendicularProjection_volume hh]
  ring

lemma physicalRuled_mem_projectedCylinder (h : ℝ) (v : Plane → Plane)
    (p g : Plane) (s : ℝ) {P : Set Plane} (hp : p + s • (v p - g) ∈ P) :
    vec3 s (p 0 + s * v p 0) (h * (p 1 + s * v p 1)) ∈
      (projectedCylinder h g P).carrier := by
  rw [projectedCylinder_mem_iff]
  refine ⟨p + s • (v p - g), hp, s, ?_⟩
  ext i
  fin_cases i <;> simp [planeEmbedding, physicalDirection, vec3] <;> ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.Frames ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma frameJacobian_pos (M : Coordinates ≃L[ℝ] Plane) : 0 < frameJacobian M := by
  apply abs_pos.mpr
  exact (M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toLinearEquiv.isUnit_det'.ne_zero

lemma frame_volume_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) : volume.real (M '' K) = frameJacobian M * volume.real K := by
  simpa using frame_integral_image M hK (fun _ => (1 : ℝ))

lemma coordinates_closedBall (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    closedBall b a = Set.pi univ (fun i => Icc (b i - a) (b i + a)) := by
  ext x
  simp only [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha, Real.norm_eq_abs,
    Pi.sub_apply, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  constructor <;> intro h i <;> obtain ⟨h₁, h₂⟩ := h i <;> constructor <;> linarith

lemma coordinates_closedBall_volume (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (closedBall b a) = (2 * a) ^ 2 := by
  rw [coordinates_closedBall b ha, measureReal_def, volume_pi_pi]
  simp only [Real.volume_Icc, add_sub_sub_cancel, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ a + a)]
  ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.LocalCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.of_fintype {ι : Type*} [Fintype ι] {shape : Cylinder → Prop}
    {S : Set Space} {A : ℝ} (C : ι → Cylinder) (hshape : ∀ i, shape (C i))
    (hcover : S ⊆ ⋃ i, (C i).carrier) (hcost : (∑ i, (C i).area) ≤ A) :
    HasFiniteCover shape S A := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, C ∘ e.symm, fun i => hshape _, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨e i, by simpa using hi⟩
  · change (∑ i : Fin (Fintype.card ι), (C (e.symm i)).area) ≤ A
    rw [e.symm.sum_comp (fun j => (C j).area)]
    exact hcost

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SquareCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Convert the finite weighted lattice certificate into actual perpendicular Euclidean cylinders.
The factor is the exact area inflation caused by the derivative remainder. -/
theorem framed_local_cover_of_shape (M : Coordinates ≃L[ℝ] Plane) {h L R delta : ℝ}
    (shape : Cylinder → Prop)
    (hshape : ∀ b : Coordinates, ∀ a : ℝ, 0 < a → ∀ g : Plane,
      shape (projectedCylinder h g (M '' closedBall b a)))
    (hh : 0 < h) (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 ≤ delta)
    {K U : Set Coordinates} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : Plane → Plane) (A : Coordinates →L[ℝ] Coordinates)
    (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖M.symm (v (M p)) - M.symm (v (M b)) - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Coordinates → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    (hFval : ∀ p ∈ U, F p = physicalWeight h (v (M p)))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h (M '' K) v L)
      (h * (1 + 2 * L * delta * R) ^ 2 *
        (∫ p in M '' K, physicalWeight h (v p)) + eps) := by
  classical
  let B : ℝ := (1 + 2 * L * delta * R) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hscale : 0 < h * frameJacobian M * B := mul_pos (mul_pos hh (frameJacobian_pos M)) hB
  obtain ⟨n, hn, S, hS, hSU, hcov, hcost⟩ := local_finite_certificate hK hU hKU
    (fun p => M.symm (v (M p))) A hL hd hmodel hrem hF hFpos (div_pos heps hscale)
  let : Fintype S := hS.fintype
  let a : ℝ := (1 / 2 + L * delta * R) / n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; positivity
  let C : S → Cylinder := fun b => projectedCylinder h (v (M b)) (M '' closedBall (b : Coordinates) a)
  have harea (b : S) : (C b).area = h * frameJacobian M * (2 * a) ^ 2 * F b := by
    dsimp only [C]
    rw [projectedCylinder_area hh, frame_volume_image M isClosed_closedBall.measurableSet,
      coordinates_closedBall_volume b ha.le, hFval b (hSU b.property)]
    ring
  have hBrel : (2 * a) ^ 2 = B / (n : ℝ) ^ 2 := by
    dsimp [a, B]
    ring
  have hintegral : (∫ p in M '' K, physicalWeight h (v p)) =
      frameJacobian M * ∫ x in K, F x := by
    rw [frame_integral_image M hK.measurableSet]
    congr 1
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    exact (hFval x (hKU hx)).symm
  apply HasFiniteCover.of_fintype C
  · intro b
    exact hshape b a ha (v (M b))
  · rintro x ⟨_, ⟨p, hp, rfl⟩, s, hs, rfl⟩
    obtain ⟨b, hb, hc⟩ := hcov p hp s hs
    apply mem_iUnion.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    apply physicalRuled_mem_projectedCylinder
    refine ⟨p + s • (M.symm (v (M p)) - M.symm (v (M b))), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      convert hc using 1
      congr 1
      module
    · simp
  · have hsum : (∑ b : S, (C b).area) =
        (h * frameJacobian M * B) * ((∑' b : S, F b) / (n : ℝ) ^ 2) := by
      simp_rw [harea, hBrel]
      rw [tsum_fintype, ← Finset.mul_sum]
      ring
    rw [hsum, hintegral]
    have hc := (mul_lt_mul_of_pos_left hcost hscale).le
    calc
      _ ≤ (h * frameJacobian M * B) *
          ((∫ x in K, F x) + eps / (h * frameJacobian M * B)) := hc
      _ = _ := by
        rw [mul_add, mul_div_cancel₀ _ hscale.ne']
        dsimp [B]
        ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.framed_local_cover_of_shape := @_root_.OAI.RuledApproximation.framed_local_cover_of_shape
