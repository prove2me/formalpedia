-- Prove2me | solution 1 for OAI.CylinderCovering.ruledHistorical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:57:05.836617+00:00
-- url     : https://prove2.me/submissions/1faab34b-e1e0-4a33-9b9d-00282253364d

import Mathlib
import Definitions.Def_CylinderCovering
import Definitions.Def_OAIQ049C000

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_CylinderBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace TriangularCovering

@[simp] theorem TriCylinder.toCylinder_axis (C : TriCylinder) :
    C.toCylinder.axis = C.axis := rfl

@[simp] theorem TriCylinder.toCylinder_carrier (C : TriCylinder) :
    C.toCylinder.carrier = C.carrier := by
  ext x
  constructor
  · rintro ⟨b, hb, t, ht⟩
    exact ⟨b, hb, t, ht⟩
  · rintro ⟨b, hb, t, ht⟩
    have hp : b ∈ normalPlane C.axis :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (C.perpendicular b hb)
    exact ⟨⟨b, hp⟩, hb, t, ht⟩

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
    all_goals try with_reducible_and_instances rfl
    simp only [finrank_euclideanSpace_fin, perpendicularPlane_finrank _ (physicalUnit_norm h g)]
  rw [hm] at hf
  rw [measureReal_def, hf, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (perpendicularProjection h g).normDet_nonneg,
    perpendicularProjection_normDet hh]
  rfl

lemma perpendicularProjection_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (perpendicularProjection h g) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hn
  have hz := LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hn
  rw [perpendicularProjection_normDet hh, physicalWeight_eq_inv_norm] at hz
  have hp : 0 < h * (1 / ‖physicalDirection h g‖) :=
    mul_pos hh (one_div_pos.mpr (physicalDirection_norm_pos h g))
  exact hp.ne' hz

lemma IsParallelogram.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsParallelogram P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsParallelogram (f '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨f c, f u, f v, ?_, ?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : (f ∘ ![u, v]) = ![f u, f v] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, by simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨c + a • u + b • v, ⟨a, ha, b, hb, rfl⟩, by simp⟩

lemma projectedCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).area = h * volume.real P * physicalWeight h g := by
  rw [Cylinder.area, projectedCylinder, perpendicularProjection_volume hh]
  ring

lemma projectedCylinder_parallelogram {h : ℝ} (hh : 0 < h) (g : Plane)
    {P : Set Plane} (hP : IsParallelogram P) :
    (projectedCylinder h g P).parallelogram :=
  hP.linear_image _ (perpendicularProjection_injective hh g)

lemma projectedCylinder_mem_iff (h : ℝ) (g : Plane) (P : Set Plane) (x : Space) :
    x ∈ (projectedCylinder h g P).carrier ↔
      ∃ p ∈ P, ∃ s : ℝ, x = planeEmbedding h p + s • physicalDirection h g := by
  have hid (p : Plane) (t : ℝ) :
      (perpendicularProjection h g p : Space) + t • physicalUnit h g =
        planeEmbedding h p +
          (t / ‖physicalDirection h g‖ -
            inner ℝ (physicalDirection h g) (planeEmbedding h p) /
              ‖physicalDirection h g‖ ^ 2) • physicalDirection h g := by
    change (planeEmbedding h p -
      (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) • physicalDirection h g) +
      t • (‖physicalDirection h g‖⁻¹ • physicalDirection h g) = _
    simp only [div_eq_mul_inv, smul_smul]
    module
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, t, rfl⟩
    exact ⟨p, hp, _, hid p t⟩
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨perpendicularProjection h g p, ⟨p, hp, rfl⟩,
      (s + inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) * ‖physicalDirection h g‖, ?_⟩
    change planeEmbedding h p + s • physicalDirection h g =
      (perpendicularProjection h g p : Space) + _ • physicalUnit h g
    rw [hid, mul_div_cancel_right₀ _ (physicalDirection_norm_pos h g).ne', add_sub_cancel_right]

lemma projectedCylinder_carrier (h : ℝ) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).carrier = firstPhysicalMap h '' auxiliaryCylinder P g := by
  ext x
  rw [projectedCylinder_mem_iff]
  constructor
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨axial s (p + s • g), ⟨s, p, hp, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]
  · rintro ⟨_, ⟨s, p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, s, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]

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
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma frameJacobian_pos (M : Coordinates ≃L[ℝ] Plane) : 0 < frameJacobian M := by
  apply abs_pos.mpr
  exact (M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toLinearEquiv.isUnit_det'.ne_zero

lemma frame_integral_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) (F : Plane → ℝ) :
    (∫ p in M '' K, F p) = frameJacobian M * (∫ x in K, F (M x)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℝ
  let D := M.trans e
  have himage : M '' K = e.symm '' (D '' K) := by
    rw [← image_comp]
    congr 1

  rw [himage]
  have hmp : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp (Fin 2)
  rw [hmp.setIntegral_image_emb e.symm.toHomeomorph.measurableEmbedding]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK
    (fun x _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn]
  rw [integral_smul]
  rfl

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

lemma coordinates_closedBall_parallelogram (b : Coordinates) {a : ℝ} (ha : 0 < a) :
    IsParallelogram (closedBall b a) := by
  let u : Coordinates := ![2*a, 0]
  let v : Coordinates := ![0, 2*a]
  refine ⟨![b 0 - a, b 1 - a], u, v, ?_, ?_⟩
  · have heq : (![u, v] : Fin 2 → Coordinates) =
        fun i => (2 * a) • Pi.basisFun ℝ (Fin 2) i := by
      funext i
      ext j
      fin_cases i <;> fin_cases j <;> simp [u, v, Pi.basisFun_apply]
    rw [heq]
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent.units_smul
      (fun _ => Units.mk0 (2 * a) (by positivity))
  · rw [coordinates_closedBall b ha.le]
    ext x
    simp only [Set.mem_pi, mem_univ, true_implies, mem_Icc, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨(x 0 - (b 0 - a)) / (2*a), ?_, (x 1 - (b 1 - a)) / (2*a), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 0).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 0).2]
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 1).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 1).2]
      · ext i
        fin_cases i <;> simp [u, v, (by positivity : 2*a ≠ 0)]
    · rintro ⟨s, hs, t, ht, rfl⟩ i
      fin_cases i <;> simp [u, v] <;> constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_PlanarIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma pairPlane_measurePreserving : MeasurePreserving pairPlaneEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma plane_integral_pair (f : Plane → ℝ) :
    (∫ z, f z) = ∫ q : ℝ × ℝ, f (vec2 q.1 q.2) :=
  (pairPlane_measurePreserving.integral_comp pairPlaneEquiv.measurableEmbedding f).symm

lemma plane_integrable_pair (f : Plane → ℝ) :
    Integrable (fun q : ℝ × ℝ => f (vec2 q.1 q.2)) ↔ Integrable f :=
  pairPlane_measurePreserving.integrable_comp_emb pairPlaneEquiv.measurableEmbedding

lemma plane_setIntegral_vertical {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ b : ℝ, ∫ r in {r : ℝ | vec2 b r ∈ S}, f (vec2 b r) := by
  rw [← integral_indicator hS,plane_integral_pair]
  rw [Measure.volume_eq_prod,integral_prod _ (by simpa only [Measure.volume_eq_prod] using (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with b
  have hm : MeasurableSet {r : ℝ | vec2 b r ∈ S} := hS.preimage (pairPlaneEquiv.measurable.comp (measurable_const.prodMk measurable_id))
  rw [← integral_indicator hm]
  rfl

lemma plane_setIntegral_horizontal {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ r : ℝ, ∫ b in {b : ℝ | vec2 b r ∈ S}, f (vec2 b r) := by
  rw [← integral_indicator hS,plane_integral_pair]
  rw [Measure.volume_eq_prod,integral_prod_symm _ (by simpa only [Measure.volume_eq_prod] using (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with r
  have hm : MeasurableSet {b : ℝ | vec2 b r ∈ S} := hS.preimage (pairPlaneEquiv.measurable.comp (measurable_id.prodMk measurable_const))
  rw [← integral_indicator hm]
  rfl

lemma plane_setIntegral_vertical_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 0 ∈ s ∧ z 1 ∈ Icc (l (z 0)) (u (z 0))) :
    (∫ z in S, f z) = ∫ b in s, ∫ r in Icc (l b) (u b), f (vec2 b r) := by
  rw [plane_setIntegral_vertical hS hf,← integral_indicator hs]
  congr 1
  funext b
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb]
    apply setIntegral_congr_set
    filter_upwards with r
    apply propext
    have hh := heq (vec2 b r)
    simp only [vec2_apply_zero,vec2_apply_one,hb,true_and] at hh
    exact hh
  · rw [Set.indicator_of_notMem hb]
    have he : {r : ℝ | vec2 b r ∈ S} = ∅ := by
      ext r
      simpa [hb] using heq (vec2 b r)
    simp [he]

lemma plane_setIntegral_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    (∫ z in S, f z) = ∫ r in s, ∫ b in Icc (l r) (u r), f (vec2 b r) := by
  rw [plane_setIntegral_horizontal hS hf,← integral_indicator hs]
  congr 1
  funext r
  by_cases hr : r ∈ s
  · rw [Set.indicator_of_mem hr]
    apply setIntegral_congr_set
    filter_upwards with b
    apply propext
    have hh := heq (vec2 b r)
    simp only [vec2_apply_zero,vec2_apply_one,hr,true_and] at hh
    exact hh
  · rw [Set.indicator_of_notMem hr]
    have he : {b : ℝ | vec2 b r ∈ S} = ∅ := by
      ext b
      simpa [hr] using heq (vec2 b r)
    simp [he]

lemma plane_volume_vertical_interval {S : Set Plane} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 0 ∈ s ∧ z 1 ∈ Icc (l (z 0)) (u (z 0))) :
    volume.real S = ∫ b in s, max (u b-l b) 0 := by
  have hi := plane_setIntegral_vertical_interval hS (integrableOn_const (C := (1:ℝ)) hfin) hs heq
  simpa [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal'] using hi

lemma plane_volume_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    volume.real S = ∫ r in s, max (u r-l r) 0 := by
  have hi := plane_setIntegral_horizontal_interval hS (integrableOn_const (C := (1:ℝ)) hfin) hs heq
  simpa [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal'] using hi

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma nearestInteger_mono : Monotone nearestInteger := by
  intro a b hab
  exact Int.floor_mono (by linarith)

lemma nearestInteger_error (t : ℝ) : |(nearestInteger t : ℝ) - t| ≤ 1 / 2 := by
  have h₁ := Int.floor_le (t + 1 / 2)
  have h₂ := Int.lt_floor_add_one (t + 1 / 2)
  unfold nearestInteger
  rw [abs_le]
  constructor <;> linarith

/-- An integer version of the monotone fixed-point argument. The bounded drift
with slope strictly less than one supplies both end barriers. -/
lemma integer_fixed_point_of_bounded_drift (F : ℤ → ℤ) (hF : Monotone F)
    (q B : ℝ) (hq : q < 1) (hB : ∀ i : ℤ, |(F i : ℝ) - q * i| ≤ B) :
    ∃ i : ℤ, F i = i := by
  have hq' : 0 < 1 - q := sub_pos.mpr hq
  obtain ⟨lo, hlo⟩ := exists_int_le (-B / (1 - q))
  obtain ⟨hi, hhi⟩ := exists_int_ge (B / (1 - q))
  have hbound : ∀ i : ℤ, F i ≤ i → lo ≤ i := by
    intro i hi
    have hb := (abs_le.mp (hB i)).1
    have hi' : (F i : ℝ) ≤ i := by exact_mod_cast hi
    have hreal : -B / (1 - q) ≤ (i : ℝ) := by
      apply (div_le_iff₀ hq').2
      nlinarith
    exact_mod_cast hlo.trans hreal
  have hhi' : F hi ≤ hi := by
    have hb := (abs_le.mp (hB hi)).2
    have ht := (div_le_iff₀ hq').1 hhi
    have : (F hi : ℝ) ≤ hi := by nlinarith
    exact_mod_cast this
  obtain ⟨i, hi, hmin⟩ := Int.exists_least_of_bdd ⟨lo, hbound⟩ ⟨hi, hhi'⟩
  exact ⟨i, le_antisymm hi (hmin (F i) (hF hi))⟩

/-- A useful strengthening of the lattice estimates: only the product
conditions are needed; either off-diagonal entry may be arbitrarily large. -/
theorem asymmetric_lattice_cover (alpha beta : ℝ)
    (hprod : 0 ≤ alpha * beta) (hprod' : alpha * beta < 1) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + alpha * j)| ≤ 1 / 2 ∧
      |u₂ - (beta * i + (j : ℝ))| ≤ 1 / 2 := by
  let F : ℤ → ℤ := fun i => nearestInteger
    (u₁ - alpha * (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ))
  have hmono : Monotone F := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    rcases mul_nonneg_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hinner : nearestInteger (u₂ - beta * (j : ℝ)) ≤
          nearestInteger (u₂ - beta * (i : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
    · have hinner : nearestInteger (u₂ - beta * (i : ℝ)) ≤
          nearestInteger (u₂ - beta * (j : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
  have hdrift : ∀ i : ℤ,
      |(F i : ℝ) - (alpha * beta) * i| ≤
        1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
    intro i
    let j := nearestInteger (u₂ - beta * (i : ℝ))
    have h₁ := nearestInteger_error (u₁ - alpha * (j : ℝ))
    have h₂ := nearestInteger_error (u₂ - beta * (i : ℝ))
    have hdecomp : (F i : ℝ) - (alpha * beta) * i =
        ((F i : ℝ) - (u₁ - alpha * j)) -
        alpha * ((j : ℝ) - (u₂ - beta * i)) + (u₁ - alpha * u₂) := by ring
    rw [hdecomp]
    calc
      _ ≤ |(F i : ℝ) - (u₁ - alpha * j)| +
          |alpha * ((j : ℝ) - (u₂ - beta * i))| + |u₁ - alpha * u₂| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
        rw [abs_mul]
        exact add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))) le_rfl
  obtain ⟨i, hi⟩ := integer_fixed_point_of_bounded_drift F hmono
    (alpha * beta) _ hprod' hdrift
  let j := nearestInteger (u₂ - beta * (i : ℝ))
  refine ⟨i, j, ?_, ?_⟩
  · have h := nearestInteger_error (u₁ - alpha * (j : ℝ))
    change |(F i : ℝ) - (u₁ - alpha * (j : ℝ))| ≤ 1 / 2 at h
    rw [hi] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← abs_neg]
    congr 1
    ring
  · have h := nearestInteger_error (u₂ - beta * (i : ℝ))
    change |(j : ℝ) - (u₂ - beta * (i : ℝ))| ≤ 1 / 2 at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← abs_neg]
    congr 1
    ring

lemma symmetric_lattice_distance (a x y : ℝ) (ha : |a| < 1)
    (hx : |x + a * y| ≤ 1 / 2) (hy : |y + a * x| ≤ 1 / 2) :
    max |x| |y| ≤ 1 / (2 * (1 - |a|)) := by
  have hax : |x| ≤ 1 / 2 + |a| * |y| := by
    calc
      |x| = |(x + a * y) - a * y| := by congr 1; ring
      _ ≤ |x + a * y| + |a * y| := abs_sub _ _
      _ ≤ 1 / 2 + |a| * |y| := by rw [abs_mul]; exact add_le_add hx le_rfl
  have hay : |y| ≤ 1 / 2 + |a| * |x| := by
    calc
      |y| = |(y + a * x) - a * x| := by congr 1; ring
      _ ≤ |y + a * x| + |a * x| := abs_sub _ _
      _ ≤ 1 / 2 + |a| * |x| := by rw [abs_mul]; exact add_le_add hy le_rfl
  have hm : max |x| |y| ≤ 1 / 2 + |a| * max |x| |y| := by
    apply max_le
    · exact hax.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_max_right _ _) (abs_nonneg a)))
    · exact hay.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_max_left _ _) (abs_nonneg a)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - |a|))).2
  nlinarith

/-- Lattice covering with a uniform distance estimate. -/
theorem lattice_covering (a : ℝ) (ha : |a| < 1) (z₁ z₂ : ℝ) :
    ∃ i j : ℤ,
      |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 ∧
      |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 ∧
      max |z₁ - i| |z₂ - j| ≤ 1 / (2 * (1 - |a|)) := by
  have haa : a * a < 1 := by nlinarith [sq_abs a, abs_nonneg a]
  obtain ⟨i, j, hi, hj⟩ := asymmetric_lattice_cover a a (mul_self_nonneg a)
    haa (z₁ + a * z₂) (z₂ + a * z₁)
  have hi' : |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 := by
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hj' : |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 := by
    convert hj using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  exact ⟨i, j, hi', hj', symmetric_lattice_distance a _ _ ha hi' hj'⟩

/-- Sliding rows have no shear bound. This is the local nilpotent model. -/
theorem sliding_rows_cover (d : ℝ) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + d * j)| ≤ 1 / 2 ∧
      |u₂ - (j : ℝ)| ≤ 1 / 2 := by
  simpa using asymmetric_lattice_cover d 0 (by simp) (by simp) u₁ u₂

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_OuterApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Closed outer neighborhoods recover a closed set even when its frontier has positive measure. -/
lemma inter_reciprocal_cthickening {E : Type*} [MetricSpace E] (K : Set E)
    (hK : IsClosed K) :
    (⋂ n : ℕ, cthickening (1 / ((n : ℝ) + 1)) K) = K := by
  apply Subset.antisymm
  · intro x hx
    have hxn : ∀ n : ℕ, infEDist x K ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      simpa only [mem_iInter, mem_cthickening_iff] using hx
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hz : infEDist x K = 0 := le_antisymm (ge_of_tendsto ht (.of_forall hxn)) bot_le
    exact hK.closure_subset (mem_closure_iff_infEDist_zero.mpr hz)
  · exact subset_iInter fun _ => self_subset_cthickening K

/-- Small open outer neighborhoods, not regularity of the label boundary, justify the weighted
lattice count for arbitrary compact label sets. -/
theorem exists_nice_outer_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [SFinite (volume : Measure E)]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : E → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ S : Set E, IsOpen S ∧ Bornology.IsBounded S ∧ K ⊆ S ∧ S ⊆ U ∧
      volume (frontier S) = 0 ∧ (∫ x in S, F x) < (∫ x in K, F x) + eps := by
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n, 0 < R n := fun n => by dsimp [R]; positivity
  have hRlim : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K' : ℕ → Set E := fun n => cthickening (R n) K
  have hK' : ∀ n, IsCompact (K' n) := fun _ => hK.cthickening
  have hanti : Antitone K' := by
    intro n m hnm
    apply cthickening_mono _ K
    dsimp [R]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hInt : Tendsto (fun n => ∫ x in K' n, F x) atTop (𝓝 (∫ x in K, F x)) := by
    have ht := tendsto_setIntegral_of_antitone (μ := volume)
      (fun n => (hK' n).measurableSet) hanti
      ⟨0, hF.continuousOn.integrableOn_compact (μ := volume) (hK' 0)⟩
    rwa [show (⋂ n, K' n) = K from inter_reciprocal_cthickening K hK.isClosed] at ht
  obtain ⟨d, hd, hdU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hevent : ∀ᶠ n in atTop, (∫ x in K' n, F x) < (∫ x in K, F x) + eps ∧ R n < d :=
    (hInt.eventually (Iio_mem_nhds (lt_add_of_pos_right _ heps))).and
      (hRlim.eventually (Iio_mem_nhds hd))
  obtain ⟨n, hnInt, hnd⟩ := hevent.exists
  obtain ⟨r, hr, hrnull⟩ := exists_null_frontier_thickening volume K (hR n)
  refine ⟨thickening r K, isOpen_thickening, hK.isBounded.thickening,
    self_subset_thickening hr.1 K, ?_, hrnull, ?_⟩
  · exact (thickening_subset_cthickening r K).trans
      ((cthickening_mono (hr.2.le.trans hnd.le) K).trans hdU)
  · have hsub : thickening r K ⊆ K' n :=
      (thickening_subset_cthickening r K).trans (cthickening_mono hr.2.le K)
    exact (setIntegral_mono_set
      (hF.continuousOn.integrableOn_compact (μ := volume) (hK' n))
      (.of_forall hFpos) (.of_forall hsub)).trans_lt hnInt

lemma finite_inter_coordinateGrid {S : Set (Fin 2 → ℝ)} (hS : Bornology.IsBounded S)
    {n : ℕ} (hn : n ≠ 0) : (S ∩ coordinateGrid n).Finite := by
  classical
  unfold coordinateGrid
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (Nat.cast_ne_zero.mpr hn))]
  exact ZSpan.setFinite_inter _ hS

/-- A finite lattice retained around any compact label set has arbitrarily accurate weighted
cost. The finite set is the intersection with a fixed regular outer neighborhood, so no
assumption on the boundary or positive area of `K` occurs here. -/
theorem finite_weighted_grid_outer {K U : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    (R : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ S : Set (Fin 2 → ℝ), S.Finite ∧
      S ⊆ U ∩ coordinateGrid n ∧
      (∀ b ∈ coordinateGrid n, (∃ p ∈ K, dist b p ≤ R / n) → b ∈ S) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨O, hOo, hOb, hKO, hOU, hOf, hOI⟩ :=
    exists_nice_outer_integral hK hU hKU hF hFpos (half_pos heps)
  obtain ⟨d, hd, hdO⟩ := hK.exists_cthickening_subset_open hOo hKO
  have hsum := tendsto_tsum_div_pow_atTop_integral O F hF hOb hOo.measurableSet hOf
  have hcost : ∀ᶠ n : ℕ in atTop,
      (∑' b : ↑(O ∩ coordinateGrid n), F b) / (n : ℝ) ^ 2 <
        (∫ p in O, F p) + eps / 2 := by
    simpa only [coordinateGrid, Fintype.card_fin] using
      hsum.eventually (Iio_mem_nhds (lt_add_of_pos_right _ (half_pos heps)))
  have hsmall : ∀ᶠ n : ℕ in atTop, R / (n : ℝ) < d := by
    have ht : Tendsto (fun n : ℕ => R / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun n : ℕ => R * (n : ℝ)⁻¹) atTop (𝓝 (R * 0)))
    exact ht.eventually (Iio_mem_nhds hd)
  filter_upwards [eventually_gt_atTop 0, hcost, hsmall] with n hn hcost hnsmall
  refine ⟨hn, O ∩ coordinateGrid n, finite_inter_coordinateGrid hOb hn.ne',
    Set.inter_subset_inter_left _ hOU, ?_, ?_⟩
  · intro b hb ⟨p, hp, hbp⟩
    exact ⟨hdO ((thickening_subset_cthickening d K)
      (mem_thickening_iff.mpr ⟨p, hp, hbp.trans_lt hnsmall⟩)), hb⟩
  · linarith

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_LocalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A quantitative derivative remainder in convex local coordinates. -/
theorem c1_local_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : E → F} {U : Set E} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : E} (hp : p ∈ U) {delta : ℝ} (hd : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      ‖v x - v y - fderiv ℝ v p (x - y)‖ ≤ delta * ‖x - y‖ := by
  have hdc : ContinuousAt (fderiv ℝ v) p :=
    (hv.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by norm_num)
  have hevent : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ v x - fderiv ℝ v p‖ < delta := by
    simpa only [dist_eq_norm] using hdc.eventually (ball_mem_nhds _ hd)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hevent (hU.mem_nhds hp))
  have hsub : ball p r ⊆ U := fun x hx => (hrsub hx).2
  refine ⟨r, hr, hsub, ?_⟩
  intro x hx y hy
  apply (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le' (φ := fderiv ℝ v p)
    (fun z hz => ((hv.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => (hrsub hz).1.le) hy hx

/-- Extending a nonnegative continuous weight from a compact patch does not alter it there. -/
theorem continuous_nonneg_extension {E : Type*} [TopologicalSpace E] [NormalSpace E]
    {K : Set E} (hK : IsClosed K) {f : E → ℝ} (hf : ContinuousOn f K)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    ∃ F : E → ℝ, Continuous F ∧ (∀ x, 0 ≤ F x) ∧ Set.EqOn F f K := by
  let fc : C(K, ℝ) := ⟨_, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK fc
  refine ⟨fun x => max (g x) 0, g.continuous.max continuous_const, fun x => le_max_right _ _, ?_⟩
  intro x hx
  have hgx : g x = f x := congrArg (fun q : C(K, ℝ) => q ⟨x, hx⟩) hg
  dsimp only
  rw [hgx, max_eq_left (hn x hx)]


/-- The nonlinear local producer. Unlike tilting a continuum of lines, it produces a
finite set of intercept centers covering every label and every time simultaneously. -/
theorem local_finite_certificate {K U : Set Parameter} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (v : Parameter → Parameter)
    (A : Parameter →L[ℝ] Parameter) {L R delta : ℝ}
    (hL : 0 ≤ L) (hdelta : 0 ≤ delta) (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖v p - v b - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Parameter → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : Set Parameter, S.Finite ∧ S ⊆ U ∧
      (∀ p ∈ K, ∀ r : ℝ, |r| ≤ L → ∃ b ∈ S,
        ‖p + r • v p - (b + r • v b)‖ ≤ (1 / 2 + L * delta * R) / n) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨n, hn, S, hSfinite, hSU, hretain, hcost⟩ :=
    (finite_weighted_grid_outer hK hU hKU hF hFpos R heps).exists
  refine ⟨n, hn, S, hSfinite, fun b hb => (hSU hb).1, ?_, hcost⟩
  intro p hp r hr
  obtain ⟨b, hbgrid, hbp, hlin⟩ := hmodel n hn p r hr
  have hbS := hretain b hbgrid ⟨p, hp, hbp⟩
  have hbp' : ‖p - b‖ ≤ R / n := by simpa [dist_eq_norm, norm_sub_rev] using hbp
  have herr := hrem p (hKU hp) b (hSU hbS).1
  refine ⟨b, hbS, ?_⟩
  calc
    ‖p + r • v p - (b + r • v b)‖ =
        ‖(p - b + r • A (p - b)) + r • (v p - v b - A (p - b))‖ := by
          congr 1
          module
    _ ≤ ‖p - b + r • A (p - b)‖ + ‖r • (v p - v b - A (p - b))‖ := norm_add_le _ _
    _ ≤ 1 / (2 * n) + L * (delta * (R / n)) := by
      apply add_le_add hlin
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_left hbp' hdelta)) hL)
    _ = (1 / 2 + L * delta * R) / n := by ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_HyperbolicLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma norm_le_of_scaled_coordinates {n C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (x : Parameter) (hx : ∀ i, |n * x i| ≤ C) : ‖x‖ ≤ C / n := by
  rw [pi_norm_le_iff_of_nonneg (div_nonneg hC hn.le)]
  intro i
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hn).2
  have := hx i
  rwa [abs_mul, abs_of_pos hn, mul_comm] at this

/-- The symmetric hyperbolic template, with its uniform distance bound. -/
theorem hyperbolic_lattice_model {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 < L * lam) (hsmall : L * lam < 1) :
    LatticeModel (lam • swapCLM) L (1 / (2 * (1 - L * lam))) := by
  have hlampos : 0 < lam := by nlinarith
  intro n hn p r hr
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have har : |r * lam| ≤ L * lam := by
    rw [abs_mul, abs_of_pos hlampos]
    exact mul_le_mul_of_nonneg_right hr hlampos.le
  have ha : |r * lam| < 1 := har.trans_lt hsmall
  obtain ⟨i, j, hi, hj, hd⟩ := lattice_covering (r * lam) ha
    ((n : ℝ) * p 0) ((n : ℝ) * p 1)
  let b : Parameter := ![(i : ℝ) / n, (j : ℝ) / n]
  have : NeZero n := ⟨hn.ne'⟩
  have hbgrid : b ∈ coordinateGrid n := by
    apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
    intro k
    fin_cases k
    · refine ⟨i, ?_⟩
      simp [b, mul_div_cancel₀, hnreal.ne']
    · refine ⟨j, ?_⟩
      simp [b, mul_div_cancel₀, hnreal.ne']
  have hd' : max |(n : ℝ) * p 0 - i| |(n : ℝ) * p 1 - j| ≤
      1 / (2 * (1 - L * lam)) := hd.trans
        (one_div_le_one_div_of_le (by positivity) (by linarith))
  refine ⟨b, hbgrid, ?_, ?_⟩
  · rw [dist_eq_norm, norm_sub_rev]
    apply norm_le_of_scaled_coordinates hnreal (by positivity)
    intro k
    fin_cases k
    · have heq : (n : ℝ) * (p - b) 0 = (n : ℝ) * p 0 - i := by
        simp [b, mul_sub, mul_div_cancel₀, hnreal.ne']
      change |(n : ℝ) * (p - b) 0| ≤ _
      rw [heq]
      exact (le_max_left _ _).trans hd'
    · have heq : (n : ℝ) * (p - b) 1 = (n : ℝ) * p 1 - j := by
        simp [b, mul_sub, mul_div_cancel₀, hnreal.ne']
      change |(n : ℝ) * (p - b) 1| ≤ _
      rw [heq]
      exact (le_max_right _ _).trans hd'
  · have hbnd : ‖p - b + r • (lam • swapCLM) (p - b)‖ ≤ (1 / 2 : ℝ) / n := by
      apply norm_le_of_scaled_coordinates hnreal (by norm_num)
      intro k
      fin_cases k
      · convert hi using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        simp [b, swapCLM, swapLinear, Matrix.vecHead, Matrix.vecTail]
        field_simp
      · convert hj using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        simp [b, swapCLM, swapLinear, Matrix.vecHead, Matrix.vecTail]
        field_simp
    convert hbnd using 1
    all_goals try with_reducible_and_instances rfl
    ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_LocalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Convert the finite weighted lattice certificate into actual perpendicular Euclidean cylinders.
The factor is the exact area inflation caused by the derivative remainder. -/
theorem framed_local_cover (M : Coordinates ≃L[ℝ] Plane) {h L R delta : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 ≤ delta)
    {K U : Set Coordinates} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : Plane → Plane) (A : Coordinates →L[ℝ] Coordinates)
    (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖M.symm (v (M p)) - M.symm (v (M b)) - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Coordinates → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    (hFval : ∀ p ∈ U, F p = physicalWeight h (v (M p)))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover Cylinder.parallelogram (physicalRuled h (M '' K) v L)
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
    apply projectedCylinder_parallelogram hh
    exact (coordinates_closedBall_parallelogram (b : Coordinates) ha).linear_image
      M.toLinearMap M.injective
  · rintro x ⟨_, ⟨p, hp, rfl⟩, s, hs, rfl⟩
    obtain ⟨b, hb, hc⟩ := hcov p hp s hs
    apply mem_iUnion.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    apply physicalRuled_mem_projectedCylinder
    refine ⟨p + s • (M.symm (v (M p)) - M.symm (v (M b))), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
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
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_HyperbolicCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma hyperbolic_frame (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 < lam)
    (hplus : Module.End.HasEigenvalue A.toLinearMap lam)
    (hminus : Module.End.HasEigenvalue A.toLinearMap (-lam)) :
    ∃ M : Coordinates ≃L[ℝ] Plane, ∀ z : Coordinates,
      M.symm (A (M z)) = ![lam * z 1, lam * z 0] := by
  obtain ⟨u, hu⟩ := hplus.exists_hasEigenvector
  obtain ⟨v, hv⟩ := hminus.exists_hasEigenvector
  have hvals : Function.Injective (![lam, -lam] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  have hli : LinearIndependent ℝ (![u, v] : Fin 2 → Plane) :=
    Module.End.eigenvectors_linearIndependent' A.toLinearMap ![lam, -lam] hvals ![u, v] (by
      intro i
      fin_cases i
      · exact hu
      · exact hv)
  let B : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  let M : Coordinates ≃L[ℝ] Plane :=
    (sumDifference.trans B.equivFun.symm).toContinuousLinearEquiv
  have hM (z : Coordinates) : M z = (z 0 + z 1) • u + (z 0 - z 1) • v := by
    simp only [M]
    simp [B, sumDifference]
  have huA : A u = lam • u := hu.apply_eq_smul
  have hvA : A v = (-lam) • v := hv.apply_eq_smul
  refine ⟨M, fun z => ?_⟩
  apply M.injective
  rw [M.apply_symm_apply, hM, map_add, map_smul, map_smul,
    huA, hvA, hM]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  module
lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma HasFiniteCover.empty (shape : Cylinder → Prop) {A : ℝ} (hA : 0 ≤ A) :
    HasFiniteCover shape ∅ A := by
  refine ⟨0, Fin.elim0, by intro i; exact i.elim0, by simp, ?_⟩
  simpa [familyArea] using hA

lemma HasFiniteCover.union {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (hS : HasFiniteCover shape S A) (hT : HasFiniteCover shape T B) :
    HasFiniteCover shape (S ∪ T) (A + B) := by
  obtain ⟨n, C, hC, hSC, hcostC⟩ := hS
  obtain ⟨m, D, hD, hTD, hcostD⟩ := hT
  refine ⟨n + m, Fin.addCases C D, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hC j
    · simpa using hD j
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hSC hx)
      exact mem_iUnion.mpr ⟨i.castAdd m, by simpa using hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hTD hx)
      exact mem_iUnion.mpr ⟨j.natAdd n, by simpa using hj⟩
  · simpa [familyArea, Fin.sum_univ_add] using add_le_add hcostC hcostD

lemma physicalRuled_union (h L : ℝ) (v : Plane → Plane) (S T : Set Plane) :
    physicalRuled h (S ∪ T) v L = physicalRuled h S v L ∪ physicalRuled h T v L := by
  ext z
  simp only [physicalRuled, mem_ofPred_eq, mem_union]
  aesop

lemma physicalRuled_empty (h L : ℝ) (v : Plane → Plane) : physicalRuled h ∅ v L = ∅ := by
  simp [physicalRuled]

/-- Compact pieces cut along a null frontier have exactly additive cost, even when
 the original compact set itself has a positive-area frontier. -/
lemma compact_cut_integral {K O : Set Plane} (hK : IsCompact K) (hO : IsOpen O)
    (hnull : volume (frontier O) = 0) {F : Plane → ℝ} (hF : IntegrableOn F K) :
    IsCompact (K ∩ closure O) ∧ IsCompact (K \ O) ∧
    K = (K ∩ closure O) ∪ (K \ O) ∧
    (∫ x in K, F x) = (∫ x in K ∩ closure O, F x) + (∫ x in K \ O, F x) := by
  have h₁ : IsCompact (K ∩ closure O) := hK.inter_right isClosed_closure
  have h₂ := hK.diff hO
  have hun : K = (K ∩ closure O) ∪ (K \ O) := by
    ext x
    simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxO : x ∈ O
      · exact Or.inl ⟨hx, subset_closure hxO⟩
      · exact Or.inr ⟨hx, hxO⟩
    · tauto
  refine ⟨h₁, h₂, hun, ?_⟩
  nth_rw 1 [hun]
  apply setIntegral_union₀
  · show volume ((K ∩ closure O) ∩ (K \ O)) = 0
    apply measure_mono_null _ hnull
    intro x hx
    rw [frontier, hO.interior_eq]
    exact ⟨hx.1.2, hx.2.2⟩
  · exact h₂.measurableSet.nullMeasurableSet
  · exact hF.mono_set inter_subset_left
  · exact hF.mono_set sdiff_subset

/-- Finite gluing over regular open patches. Only the patch frontiers must be null;
 there is deliberately no restriction on the label set's own frontier. -/
theorem glue_finite_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) {A : ℝ}
    {ι : Type*} (s : Finset ι) (O U : ι → Set Plane)
    (hO : ∀ i ∈ s, IsOpen (O i)) (hOU : ∀ i ∈ s, closure (O i) ⊆ U i)
    (hnull : ∀ i ∈ s, volume (frontier (O i)) = 0)
    (hlocal : ∀ i ∈ s, ∀ Q : Set Plane, IsCompact Q → Q ⊆ U i →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover shape (physicalRuled h Q v L)
        (A * (∫ p in Q, F p) + eps))
    {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hcover : K ⊆ ⋃ i ∈ s, O i) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ p in K, F p) + eps) := by
  classical
  induction s using Finset.induction_on generalizing K eps with
  | empty =>
    have hKe : K = ∅ := by simpa using hcover
    rw [hKe, physicalRuled_empty]
    simpa using HasFiniteCover.empty shape heps.le
  | @insert i s hi ih =>
    have hOi := hO i (by simp)
    obtain ⟨h₁, h₂, hun, hint⟩ := compact_cut_integral hK hOi (hnull i (by simp)) hF
    have hc₁ := hlocal i (by simp) _ h₁
      (inter_subset_right.trans (hOU i (by simp))) (eps / 2) (half_pos heps)
    have hsub : K \ O i ⊆ ⋃ j ∈ s, O j := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hx.1)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (hx.2 hxj)
      · exact mem_iUnion₂.mpr ⟨j, hj, hxj⟩
    have hc₂ := ih (fun j hj => hO j (by simp [hj]))
      (fun j hj => hOU j (by simp [hj])) (fun j hj => hnull j (by simp [hj]))
      (fun j hj => hlocal j (by simp [hj])) h₂ (hF.mono_set sdiff_subset)
      hsub (half_pos heps)
    have hc := hc₁.union hc₂
    rw [← physicalRuled_union, ← hun] at hc
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rw [hint]
    ring

lemma physicalWeight_pos (h : ℝ) (g : Plane) : 0 < physicalWeight h g := by
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

lemma exists_small_inflation (L R : ℝ) {B : ℝ} (hB : 1 < B) :
    ∃ delta : ℝ, 0 < delta ∧ (1 + 2 * L * delta * R) ^ 2 < B := by
  have hc : Continuous (fun d : ℝ => (1 + 2 * L * d * R) ^ 2) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1 + 2 * L * d * R) ^ 2 < B :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hB))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- Every hyperbolic label has a patch whose compact subsets admit finite covers,
with one prescribed arbitrarily small area inflation. -/
theorem hyperbolic_local_patch {h L B : ℝ} (hh : 0 < h) (hL : 0 < L) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hhyp : HyperbolicAt L v p) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover Cylinder.parallelogram (physicalRuled h K v L)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by
  obtain ⟨lam, hlam, hsmall, hplus, hminus⟩ := hhyp
  have hlampos : 0 < lam := by nlinarith
  obtain ⟨M, hM⟩ := hyperbolic_frame (fderiv ℝ v p) hlampos hplus hminus
  let A : Coordinates →L[ℝ] Coordinates := lam • swapCLM
  let R : ℝ := 1 / (2 * (1 - L * lam))
  have hR : 0 < R := by dsimp [R]; positivity
  have hmodel : LatticeModel A L R := hyperbolic_lattice_model hL hlam hsmall
  obtain ⟨delta, hd, hDB⟩ := exists_small_inflation L R hB
  let w : Coordinates → Coordinates := fun x => M.symm (v (M x))
  let Uc : Set Coordinates := M ⁻¹' U
  have hUco : IsOpen Uc := hU.preimage M.continuous
  have hpc : M.symm p ∈ Uc := by simpa [Uc]
  have hvc : ContDiffOn ℝ 1 (fun x => v (M x)) Uc :=
    hv.comp M.contDiff.contDiffOn (fun x hx => hx)
  have hwc : ContDiffOn ℝ 1 w Uc := M.symm.contDiff.comp_contDiffOn hvc
  have hvder := (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hwd : fderiv ℝ w (M.symm p) = A := by
    have hvd : HasFDerivAt (fun x => v (M x))
        ((fderiv ℝ v p).comp M.toContinuousLinearMap) (M.symm p) := by
      have hvdp : HasFDerivAt v (fderiv ℝ v p) (M (M.symm p)) := by
        simpa using hvder.hasFDerivAt
      exact hvdp.comp (M.symm p) M.hasFDerivAt
    have hcomp := M.symm.hasFDerivAt.comp (M.symm p) hvd
    change fderiv ℝ (M.symm ∘ (fun x => v (M x))) (M.symm p) = A
    rw [hcomp.fderiv]
    ext z i
    have hz := congrArg (fun a : Coordinates => a i) (hM z)
    fin_cases i <;> simpa [A, swapCLM, swapLinear] using hz
  obtain ⟨r, hr, hrU, hrem⟩ := c1_local_remainder hUco hwc hpc hd
  let Vc := ball (M.symm p) (r / 2)
  have hrhalf : r / 2 < r := by linarith
  have hclU : closedBall (M.symm p) (r / 2) ⊆ Uc :=
    (closedBall_subset_ball hrhalf).trans hrU
  have hclF : ContinuousOn (fun x => physicalWeight h (v (M x)))
      (closedBall (M.symm p) (r / 2)) :=
    (physicalWeight_continuous h).comp_continuousOn (hvc.continuousOn.mono hclU)
  obtain ⟨F, hF, hFnon, hFeq⟩ := continuous_nonneg_extension isClosed_closedBall hclF
    (fun x _ => (physicalWeight_pos h (v (M x))).le)
  refine ⟨M '' Vc, M.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · exact ⟨M.symm p, mem_ball_self (half_pos hr), M.apply_symm_apply p⟩
  · intro K hK hKV eps heps
    let Kc := M.symm '' K
    have hKc : IsCompact Kc := hK.image M.symm.continuous
    have hKcV : Kc ⊆ Vc := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKV hq
      simpa using hx
    have himg : M '' Kc = K := by simp [Kc]
    have hc := framed_local_cover M hh hL.le hR.le hd.le hKc isOpen_ball hKcV v A hmodel
      (fun x hx y hy => by
        rw [← hwd]
        exact hrem x (ball_subset_ball hrhalf.le hx) y (ball_subset_ball hrhalf.le hy))
      hF hFnon (fun x hx => hFeq (ball_subset_closedBall hx)) heps
    rw [himg] at hc
    apply hc.mono Subset.rfl
    have hI : 0 ≤ ∫ q in K, physicalWeight h (v q) :=
      integral_nonneg (fun q => (physicalWeight_pos h (v q)).le)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB.le hh.le) hI]

/-- Compactness and null-frontier patches globalize the finite local producer. -/
theorem globalize_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) (A : ℝ) {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hpatch : ∀ p ∈ K, ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧
      ∀ Q : Set Plane, IsCompact Q → Q ⊆ V → ∀ eps : ℝ, 0 < eps →
      HasFiniteCover shape (physicalRuled h Q v L) (A * (∫ q in Q, F q) + eps))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ q in K, F q) + eps) := by
  classical
  choose V hVo hpV hloc using fun p : K => hpatch p p.property
  choose r hr hrV using fun p : K => Metric.mem_nhds_iff.mp ((hVo p).mem_nhds (hpV p))
  let O : K → Set Plane := fun p => ball (p : Plane) (r p / 2)
  have hOo : ∀ p : K, IsOpen (O p) := fun _ => isOpen_ball
  have hcover : K ⊆ ⋃ p : K, O p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (half_pos (hr ⟨p, hp⟩))⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hOo hcover
  apply glue_finite_local_covers h L v F s O V (fun p _ => hOo p) _ _
    (fun p _ => hloc p) hK hF hs heps
  · intro p _
    rw [show O p = ball (p : Plane) (r p / 2) from rfl,
      closure_ball (p : Plane) (half_pos (hr p)).ne']
    exact (closedBall_subset_ball (by linarith [hr p])).trans (hrV p)
  · intro p _
    apply measure_mono_null frontier_ball_subset_sphere
    exact MeasureTheory.Measure.addHaar_sphere volume (p : Plane) (r p / 2)

lemma exists_inflation_budget (C : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 < B ∧ B * C < C + eps := by
  have hc : Continuous (fun d : ℝ => (1+d)*C) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1+d)*C < C + eps :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using lt_add_of_pos_right C heps))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1+r/2, by linarith, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- General physical weighted hyperbolic approximation, before isometry transport. -/
theorem physical_hyperbolic_cover {h L : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hL : 0 < L) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hhyp : ∀ p ∈ D, HyperbolicAt L v p) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover Cylinder.parallelogram (physicalRuled h D v L)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h L v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => hyperbolic_local_patch hh hL hB hU hv (hDU hp) (hhyp p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Isometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsParallelogram P) (a : E) :
    IsParallelogram ((fun x => a + x) '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨a+c, u, v, hli, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨s, hs, t, ht, by abel_nf⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨c+s•u+t•v, ⟨s, hs, t, ht, rfl⟩, by abel_nf⟩

lemma Cylinder.rotate_carrier (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).carrier = R '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    exact ⟨(b : Space) + t • C.axis, ⟨b, hb, t, rfl⟩, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    exact ⟨rotatedPlane C.axis R b, ⟨b, hb, rfl⟩, t, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩

lemma Cylinder.rotate_area (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).area = C.area := by
  change volume.real (rotatedPlane C.axis R '' C.base) = volume.real C.base
  have he := (rotatedPlane C.axis R).measurePreserving.setIntegral_image_emb
    (rotatedPlane C.axis R).toHomeomorph.measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.rotate_parallelogram {C : Cylinder} (hC : C.parallelogram)
    (R : Space ≃ₗᵢ[ℝ] Space) : (C.rotate R).parallelogram :=
  hC.linear_image (rotatedPlane C.axis R).toLinearMap (rotatedPlane C.axis R).injective

lemma Cylinder.translate_carrier (C : Cylinder) (q : Space) :
    (C.translate q).carrier = (fun x => q + x) '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    refine ⟨(b : Space) + (t - inner ℝ C.axis q) • C.axis,
      ⟨b, hb, _, rfl⟩, ?_⟩
    change q + ((b : Space) + (t - inner ℝ C.axis q) • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + t • C.axis
    module
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    refine ⟨C.transversePart q + b, ⟨b, hb, rfl⟩, t + inner ℝ C.axis q, ?_⟩
    change q + ((b : Space) + t • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + (t + inner ℝ C.axis q) • C.axis
    module

lemma Cylinder.translate_area (C : Cylinder) (q : Space) :
    (C.translate q).area = C.area := by
  change volume.real ((fun b => C.transversePart q + b) '' C.base) = volume.real C.base
  have he := (measurePreserving_add_left volume (C.transversePart q)).setIntegral_image_emb
    (Homeomorph.addLeft (C.transversePart q)).measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.translate_parallelogram {C : Cylinder} (hC : C.parallelogram) (q : Space) :
    (C.translate q).parallelogram := hC.translate (C.transversePart q)

/-- Exact Euclidean isometry transport preserves finite covers and perpendicular area. -/
lemma HasFiniteCover.isometry {S : Set Space} {A : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (F : Space ≃ᵢ Space) :
    HasFiniteCover Cylinder.parallelogram (F '' S) A := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := hc
  let R := F.toRealLinearIsometryEquiv
  have hF (x : Space) : F x = F 0 + R x := by
    simp [R, IsometryEquiv.toRealLinearIsometryEquiv_apply]
  let D : Fin n → Cylinder := fun i => ((C i).rotate R).translate (F 0)
  refine ⟨n, D, fun i => Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram (hC i) R) (F 0), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change F x ∈ (((C i).rotate R).translate (F 0)).carrier
    rw [Cylinder.translate_carrier, Cylinder.rotate_carrier]
    exact ⟨R x, ⟨x, hi, rfl⟩, (hF x).symm⟩
  · simpa [familyArea, D, Cylinder.translate_area, Cylinder.rotate_area] using hcost

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Hyperbolic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Scaled-plane approximation under every Euclidean isometry. -/
theorem physicalHyperbolic : PhysicalHyperbolicStatement := by
  intro h L D v hh hL hD hv hH e he F
  exact (physical_hyperbolic_cover hh hL hD hv hH he).isometry F

lemma norm_plane_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma physicalWeight_one (g : Plane) : physicalWeight 1 g = weight g := by
  simp only [physicalWeight, weight, norm_plane_sq, one_pow, one_mul]
  congr 2
  ring

lemma cycle_physicalRuled (D : Set Plane) (v : Plane → Plane) (L : ℝ) :
    cycleCoordinates '' physicalRuled 1 D v L = ruled D v L := by
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, r, hr, rfl⟩, rfl⟩
    exact ⟨p, hp, r, hr, by simp [cycleCoordinates]⟩
  · rintro ⟨p, hp, r, hr, rfl⟩
    refine ⟨vec3 r (p 0+r*v p 0) (p 1+r*v p 1),
      ⟨p, hp, r, hr, by simp⟩, ?_⟩
    rfl

/-- General hyperbolic approximation: arbitrary compact labels, including
positive-area frontiers and area-zero sets. -/
theorem hyperbolic : HyperbolicStatement := by
  intro D v L hD hv hL hH e he
  have hc := physicalHyperbolic 1 L D v (by norm_num) hL hD hv hH e he
    cycleCoordinates.toIsometryEquiv
  simpa only [LinearIsometryEquiv.coe_toIsometryEquiv, cycle_physicalRuled,
    physicalWeight_one, one_mul] using hc

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SpecializedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsParallelogram P) : IsCompact P := by
  obtain ⟨c, u, v, _, rfl⟩ := hP
  have hc : IsCompact ((fun z : ℝ × ℝ => c + z.1 • u + z.2 • v) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨(s,t), ⟨hs,ht⟩, rfl⟩
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
    exact ⟨s,hs,t,ht,rfl⟩

lemma Cylinder.enlarge_open {C : Cylinder} (hC : C.parallelogram) {eps : ℝ} (heps : 0 < eps) :
    ∃ D : Cylinder, D.openBounded ∧ C.carrier ⊆ D.carrier ∧ D.area < C.area + eps := by
  obtain ⟨O, hOo, hOb, hCO, _, _, hOI⟩ := exists_nice_outer_integral
    hC.isCompact isOpen_univ (subset_univ _) (continuous_const : Continuous (fun _ => (1 : ℝ)))
    (fun _ => zero_le_one) heps
  refine ⟨⟨C.axis, C.unit_axis, O⟩, ⟨hOo,hOb,hOo.measurableSet⟩, ?_, ?_⟩
  · rintro x ⟨b,hb,t,hx⟩
    exact ⟨b,hCO hb,t,hx⟩
  · change volume.real O < volume.real C.base + eps
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using hOI

/-- Compact parallelogram covers admit bounded open perpendicular bases with any
additional positive error. No portion of the closed ruled family is discarded. -/
lemma HasFiniteCover.open_enlarge {S : Set Space} {A eps : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (heps : 0 < eps) :
    HasFiniteCover Cylinder.openBounded S (A+eps) := by
  classical
  obtain ⟨n,C,hC,hcov,hcost⟩ := hc
  have hd : 0 < eps / (n+1 : ℝ) := div_pos heps (by positivity)
  choose D hD hCD harea using fun i => Cylinder.enlarge_open (hC i) hd
  refine ⟨n,D,hD,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨i,hCD i hi⟩
  · change (∑ i, (D i).area) ≤ A+eps
    calc
      _ ≤ ∑ i, ((C i).area + eps/(n+1 : ℝ)) := Finset.sum_le_sum (fun i _ => (harea i).le)
      _ = familyArea C + n * (eps/(n+1 : ℝ)) := by simp [familyArea, Finset.sum_add_distrib]
      _ ≤ A + eps := by
        have hn : 0 < (n+1 : ℝ) := by positivity
        have hne : (n : ℝ) * (eps/(n+1 : ℝ)) ≤ eps := by
          rw [← mul_div_assoc, div_le_iff₀ hn]
          nlinarith
        exact add_le_add hcost hne

/-- The product-cell endpoint follows from the stronger arbitrary-compact producer
and exact open-base enlargement. -/
theorem productCell : ProductCellStatement := by
  intro h M D v hh hM hD _ hv hH e he
  have hc := physical_hyperbolic_cover hh hM hD hv hH (half_pos he)
  have ho := hc.open_enlarge (half_pos he)
  convert ho using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma plane_charpoly (A : Plane →ₗ[ℝ] Plane) :
    A.charpoly = Polynomial.X ^ 2 -
      Polynomial.C (LinearMap.trace ℝ Plane A) * Polynomial.X + Polynomial.C (LinearMap.det A) := by
  rw [← LinearMap.charpoly_toMatrix A (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.charpoly_fin_two, LinearMap.det_toMatrix,
    ← LinearMap.trace_eq_matrix_trace]

lemma plane_hyperbolic_eigenvalues (A : Plane →ₗ[ℝ] Plane)
    (ht : LinearMap.trace ℝ Plane A = 0) (hd : LinearMap.det A < 0) :
    Module.End.HasEigenvalue A (Real.sqrt (-LinearMap.det A)) ∧
    Module.End.HasEigenvalue A (-Real.sqrt (-LinearMap.det A)) := by
  have hs : Real.sqrt (-LinearMap.det A) ^ 2 = -LinearMap.det A :=
    Real.sq_sqrt (by linarith)
  constructor <;> rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly, ht] <;> simp [hs]

lemma eigenvalue_le_norm (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Module.End.HasEigenvalue A.toLinearMap lam) : lam ≤ ‖A‖ := by
  obtain ⟨u, hu⟩ := h.exists_hasEigenvector
  have hue : A u = lam • u := hu.apply_eq_smul
  have hn := A.le_opNorm u
  rw [hue, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hn
  exact le_of_mul_le_mul_right hn (norm_pos_iff.mpr hu.2)

lemma eigenvalue_smul (A : Plane →ₗ[ℝ] Plane) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue A lam) (k : ℝ) :
    Module.End.HasEigenvalue (k • A) (k * lam) := by
  obtain ⟨u, hu⟩ := hlam.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change k • A u = (k*lam) • u
    rw [hu.apply_eq_smul, mul_smul]
  · exact hu.2

/-- The orthogonal-grid endpoint needs no new cover construction: its norm bound
implies precisely the two-eigenvalue condition of the general theorem. -/
theorem orthogonalGrid : OrthogonalGridStatement := by
  intro D v kappa hD _ hv hk hH e he
  have hhyp : ∀ p ∈ D, HyperbolicAt 1 v p := by
    intro p hp
    obtain ⟨ht,hd,hn⟩ := hH p hp
    obtain ⟨hplus,hminus⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap ht hd
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hd)
    refine ⟨_, by simpa using hlam, ?_, hplus, hminus⟩
    simpa only [one_mul] using ((eigenvalue_le_norm _ hlam.le hplus).trans hn).trans_lt hk
  have hc := physical_hyperbolic_cover (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
    (by norm_num : (0:ℝ)<1) hD hv hhyp he
  simpa only [physicalWeight, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] using hc

lemma OpenRectangleC2.smoothNear {D : Set Plane} {v : Plane → Plane}
    (hv : OpenRectangleC2 D v) : SmoothNear 1 D v := by
  obtain ⟨a,b,_,hD,hv⟩ := hv
  refine ⟨{p | ∀ i, p i ∈ Ioo (a i) (b i)}, ?_,hD,hv.of_le (by norm_num)⟩
  have he : {p : Plane | ∀ i, p i ∈ Ioo (a i) (b i)} =
      ⋂ i : Fin 2, (fun p : Plane => p i) ⁻¹' Ioo (a i) (b i) := by ext p; simp
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (by fun_prop))

/-- The logarithmic-cell endpoint follows with its exact velocity scaling and
orthonormal-coordinate weight, while its boundary hypothesis remains local. -/
theorem logarithmic : LogarithmicStatement := by
  intro X k D v hX hk hD _ hv hH e he
  obtain ⟨U,hU,hDU,hv1⟩ := hv.smoothNear
  have hw : SmoothNear 1 D (fun p => k • v p) :=
    ⟨U,hU,hDU,hv1.const_smul k⟩
  have hhyp : ∀ p ∈ D, HyperbolicAt X (fun p => k • v p) p := by
    intro p hp
    obtain ⟨ht,hd,hsmall⟩ := hH p hp
    obtain ⟨hplus,hminus⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap ht hd
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hd)
    have hder := ((hv1.contDiffAt (hU.mem_nhds (hDU hp))).differentiableAt
      (by norm_num)).hasFDerivAt.const_smul k
    have hf : fderiv ℝ (fun p => k • v p) p = k • fderiv ℝ v p := hder.fderiv
    refine ⟨k*Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap), by positivity,
      by nlinarith, ?_, ?_⟩
    · rw [hf]
      exact eigenvalue_smul _ hplus k
    · rw [hf]
      change Module.End.HasEigenvalue (k • (fderiv ℝ v p).toLinearMap) (- (k * _))
      rw [← mul_neg]
      exact eigenvalue_smul _ hminus k
  have hc := physical_hyperbolic_cover (by norm_num : (0:ℝ)<1) hX hD hw hhyp (half_pos he)
  have ho := hc.open_enlarge (half_pos he)
  convert ho using 1
  all_goals try with_reducible_and_instances rfl
  rw [one_mul]
  have hint : (∫ p in D, physicalWeight 1 (k • v p)) =
      ∫ p in D, 1 / Real.sqrt (1 + k ^ 2 * ‖v p‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [] with p
    rw [physicalWeight_one, weight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hint]
  ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_NilpotentLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A square-zero planar operator has an orthonormal shear frame, with no bound
on the shear coefficient. -/
lemma nilpotent_frame (A : Plane →L[ℝ] Plane) (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ d : ℝ, ∀ z : Plane,
      R.symm (A (R z)) = vec2 (d * z 1) 0 := by
  classical
  have hAA (x : Plane) : A (A x) = 0 := by
    have hh := congrArg (fun T : Plane →L[ℝ] Plane => T x) hA
    exact hh
  have hex : ∃ u : Plane, ‖u‖ = 1 ∧ A u = 0 := by
    by_cases hz : A = 0
    · refine ⟨vec2 1 0, ?_, by simp [hz]⟩
      simp [vec2, EuclideanSpace.norm_eq]
    · have hx : ∃ x : Plane, A x ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        apply ContinuousLinearMap.ext
        exact h
      obtain ⟨x, hx⟩ := hx
      refine ⟨‖A x‖⁻¹ • A x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      · simp [hAA]
  obtain ⟨u, hu, hAu⟩ := hex
  have hon : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp i.property)
    have hj : j = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp j.property)
    subst i
    subst j
    simp [hu]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let R : Plane ≃ₗᵢ[ℝ] Plane := b.repr.symm
  have hb0 : b 0 = u := hb 0 (by simp)
  have hrepr0 : b.repr (A (b 0)) = 0 := by rw [hb0, hAu, map_zero]
  let W : Plane →ₗ[ℝ] Plane := b.repr.toLinearMap.comp (A.toLinearMap.comp b.repr.symm.toLinearMap)
  have he0 : vec2 1 0 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hW0 : W (vec2 1 0) = 0 := by
    change b.repr (A (b.repr.symm (vec2 1 0))) = 0
    rw [he0, b.repr_symm_single]
    exact hrepr0
  have hWW (z : Plane) : W (W z) = 0 := by
    simp [W, hAA]
  have hexp (z : Plane) : z = z 0 • vec2 1 0 + z 1 • vec2 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hWexp (z : Plane) : W z = z 1 • W (vec2 0 1) := by
    nth_rw 1 [hexp z]
    rw [map_add, map_smul, map_smul, hW0, smul_zero, zero_add]
  have hz11 : W (vec2 0 1) 1 = 0 := by
    have hs := congrArg (fun z : Plane => z 1) (hWW (vec2 0 1))
    rw [hWexp (W (vec2 0 1))] at hs
    change W (vec2 0 1) 1 * W (vec2 0 1) 1 = 0 at hs
    exact mul_self_eq_zero.mp hs
  refine ⟨R, W (vec2 0 1) 0, fun z => ?_⟩
  change W z = _
  rw [hWexp]
  ext i
  fin_cases i
  · change z 1 * W (vec2 0 1) 0 = W (vec2 0 1) 0 * z 1
    ring
  · change z 1 * W (vec2 0 1) 1 = 0
    rw [hz11, mul_zero]

/-- A sliding-row lattice for every real shear; the retained radius is finite
but no smallness of the derivative is imposed. -/
theorem nilpotent_lattice_model (d : ℝ) :
    LatticeModel (d • shearCLM) 1 ((1+|d|)/2) := by
  intro n hn p r hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i,j,hi,hj⟩ := sliding_rows_cover (r*d)
    ((n:ℝ)*p 0 + r*d*((n:ℝ)*p 1)) ((n:ℝ)*p 1)
  have hrd : |r*d| ≤ |d| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hr (abs_nonneg d)
  have hd0 : |(n:ℝ)*p 0-i| ≤ (1+|d|)/2 := by
    have heq : (n:ℝ)*p 0-i =
        ((n:ℝ)*p 0+r*d*((n:ℝ)*p 1)-(i+r*d*j))-r*d*((n:ℝ)*p 1-j) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by
      rw [abs_mul]
      have hm := mul_le_mul hrd hj (abs_nonneg _) (abs_nonneg d)
      linarith)
  let b : Coordinates := ![(i:ℝ)/n,(j:ℝ)/n]
  let : NeZero n := ⟨hn.ne'⟩
  have hb : b ∈ coordinateGrid n := by
    apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
    intro k
    fin_cases k
    · exact ⟨i, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
    · exact ⟨j, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
  refine ⟨b,hb,?_,?_⟩
  · rw [dist_eq_norm, norm_sub_rev]
    apply norm_le_of_scaled_coordinates hnR (by positivity)
    intro k
    fin_cases k
    · simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hd0
    · have hj' : |(n:ℝ)*p 1-j| ≤ (1+|d|)/2 := by linarith [abs_nonneg d]
      simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hj'
  · have hbnd : ‖p-b+r • (d • shearCLM) (p-b)‖ ≤ (1/2:ℝ)/n := by
      apply norm_le_of_scaled_coordinates hnR (by norm_num)
      intro k
      fin_cases k
      · convert hi using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
        ring
      · convert hj using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
    convert hbnd using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma orthogonal_closedBall_square (R : Plane ≃ₗᵢ[ℝ] Plane) (b : Coordinates)
    {a : ℝ} (ha : 0 < a) :
    IsSquareTile (orthogonalFrame R '' closedBall b a) := by
  let M := orthogonalFrame R
  refine ⟨M b,R,2*a,by positivity,?_⟩
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    let q : Coordinates := fun i => (x i-b i)/(2*a)
    refine ⟨WithLp.toLp 2 q, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha.le] at hx
      intro i
      change |(x i-b i)/(2*a)| ≤ 1/2
      rw [abs_div, abs_of_pos (by positivity : 0 < 2*a)]
      apply (div_le_iff₀ (by positivity : 0 < 2*a)).mpr
      have hi := hx i
      change |x i-b i| ≤ a at hi
      linarith
    · change M b+(2*a) • M q = M x
      rw [← map_smul, ← map_add]
      congr 1
      ext i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,q]
      rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) ha.ne')]
      ring
  · rintro ⟨x,hx,rfl⟩
    refine ⟨b+(2*a) • WithLp.ofLp x, ?_, ?_⟩
    · rw [coordinates_closedBall b ha.le]
      intro i _
      change b i-a ≤ b i+(2*a)*x i ∧ b i+(2*a)*x i ≤ b i+a
      have hi := abs_le.mp (hx i)
      constructor <;> nlinarith [hi.1,hi.2]
    · change M (b+(2*a) • WithLp.ofLp x) = M b + (2*a) • R x
      simp [M,orthogonalFrame]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SquareCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
      all_goals try with_reducible_and_instances rfl
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


/-- Every square-zero label has a patch whose compact subsets admit finite covers,
with one prescribed arbitrarily small area inflation. -/
theorem nilpotent_local_patch {h B : ℝ} (hh : 0 < h) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hnil : (fderiv ℝ v p).comp (fderiv ℝ v p) = 0) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover (squareProjected h) (physicalRuled h K v 1)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by
  obtain ⟨Q, d, hQ⟩ := nilpotent_frame (fderiv ℝ v p) hnil
  let M := orthogonalFrame Q
  have hM (z : Coordinates) : M.symm ((fderiv ℝ v p) (M z)) = ![d*z 1,0] := by
    have hz := congrArg WithLp.ofLp (hQ (WithLp.toLp 2 z))
    exact hz
  let A : Coordinates →L[ℝ] Coordinates := d • shearCLM
  let R : ℝ := (1+|d|)/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hmodel : LatticeModel A 1 R := nilpotent_lattice_model d
  obtain ⟨delta, hd, hDB⟩ := exists_small_inflation 1 R hB
  let w : Coordinates → Coordinates := fun x => M.symm (v (M x))
  let Uc : Set Coordinates := M ⁻¹' U
  have hUco : IsOpen Uc := hU.preimage M.continuous
  have hpc : M.symm p ∈ Uc := by simpa [Uc]
  have hvc : ContDiffOn ℝ 1 (fun x => v (M x)) Uc :=
    hv.comp M.contDiff.contDiffOn (fun x hx => hx)
  have hwc : ContDiffOn ℝ 1 w Uc := M.symm.contDiff.comp_contDiffOn hvc
  have hvder := (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hwd : fderiv ℝ w (M.symm p) = A := by
    have hvd : HasFDerivAt (fun x => v (M x))
        ((fderiv ℝ v p).comp M.toContinuousLinearMap) (M.symm p) := by
      have hvdp : HasFDerivAt v (fderiv ℝ v p) (M (M.symm p)) := by
        simpa using hvder.hasFDerivAt
      exact hvdp.comp (M.symm p) M.hasFDerivAt
    have hcomp := M.symm.hasFDerivAt.comp (M.symm p) hvd
    change fderiv ℝ (M.symm ∘ (fun x => v (M x))) (M.symm p) = A
    rw [hcomp.fderiv]
    ext z i
    have hz := congrArg (fun a : Coordinates => a i) (hM z)
    fin_cases i <;> simpa [A, shearCLM, shearLinear] using hz
  obtain ⟨r, hr, hrU, hrem⟩ := c1_local_remainder hUco hwc hpc hd
  let Vc := ball (M.symm p) (r / 2)
  have hrhalf : r / 2 < r := by linarith
  have hclU : closedBall (M.symm p) (r / 2) ⊆ Uc :=
    (closedBall_subset_ball hrhalf).trans hrU
  have hclF : ContinuousOn (fun x => physicalWeight h (v (M x)))
      (closedBall (M.symm p) (r / 2)) :=
    (physicalWeight_continuous h).comp_continuousOn (hvc.continuousOn.mono hclU)
  obtain ⟨F, hF, hFnon, hFeq⟩ := continuous_nonneg_extension isClosed_closedBall hclF
    (fun x _ => (physicalWeight_pos h (v (M x))).le)
  refine ⟨M '' Vc, M.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · exact ⟨M.symm p, mem_ball_self (half_pos hr), M.apply_symm_apply p⟩
  · intro K hK hKV eps heps
    let Kc := M.symm '' K
    have hKc : IsCompact Kc := hK.image M.symm.continuous
    have hKcV : Kc ⊆ Vc := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKV hq
      simpa using hx
    have himg : M '' Kc = K := by simp [Kc]
    have hc := framed_local_cover_of_shape M (squareProjected h)
      (fun b a ha g => ⟨_,g,orthogonal_closedBall_square Q b ha,rfl⟩)
      hh (by norm_num : (0:ℝ)≤1) hR.le hd.le hKc isOpen_ball hKcV v A hmodel
      (fun x hx y hy => by
        rw [← hwd]
        exact hrem x (ball_subset_ball hrhalf.le hx) y (ball_subset_ball hrhalf.le hy))
      hF hFnon (fun x hx => hFeq (ball_subset_closedBall hx)) heps
    rw [himg] at hc
    apply hc.mono Subset.rfl
    have hI : 0 ≤ ∫ q in K, physicalWeight h (v q) :=
      integral_nonneg (fun q => (physicalWeight_pos h (v q)).le)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB.le hh.le) hI]

/-- Finite square-tile approximation, with unrestricted local shear and arbitrary
compact labels. -/
theorem nilpotent_physical_cover {h : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hnil : ∀ p ∈ D, (fderiv ℝ v p).comp (fderiv ℝ v p) = 0)
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D v 1)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h 1 v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => nilpotent_local_patch hh hB hU hv (hDU hp) (hnil p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

lemma unitSquare_parallelogram : IsParallelogram unitSquare := by
  have he : unitSquare = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
      closedBall (0 : Coordinates) (1/2:ℝ) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
      exact hx
    · rintro ⟨y,hy,rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hy
      exact hy
  rw [he]
  exact (coordinates_closedBall_parallelogram 0 (by norm_num : (0:ℝ)<1/2)).linear_image
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective

lemma IsSquareTile.parallelogram {T : Set Plane} (hT : IsSquareTile T) :
    IsParallelogram T := by
  obtain ⟨c,R,a,ha,rfl⟩ := hT
  have hi : Function.Injective (a • R.toLinearMap) := by
    intro x y hxy
    apply R.injective
    exact (smul_right_injective Plane ha.ne') hxy
  have he : (fun x => c+a • R x) '' unitSquare =
      (fun x => c+x) '' ((a • R.toLinearMap) '' unitSquare) := by
    rw [← image_comp]
    rfl
  rw [he]
  exact (unitSquare_parallelogram.linear_image (a • R.toLinearMap) hi).translate c

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Nilpotent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma physicalMaps_relation (h a : ℝ) (z : Space) :
    secondPhysicalMap h a z = vec3 0 0 (h*a) + swapReflect (firstPhysicalMap h z) := by
  ext i
  fin_cases i <;> simp [secondPhysicalMap,firstPhysicalMap,swapReflect,vec3]; ring

lemma firstPhysicalMap_injective {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (firstPhysicalMap h) := by
  intro x y he
  have he0 := congrArg (fun z : Space => z 0) he
  have he1 := congrArg (fun z : Space => z 1) he
  have he2 := congrArg (fun z : Space => z 2) he
  ext i
  fin_cases i
  · exact he0
  · exact he1
  · exact (mul_left_cancel₀ hh he2)

lemma firstPhysicalMap_ruled (h : ℝ) (D : Set Plane) (G : Plane → Plane) :
    firstPhysicalMap h '' physicalRuled 1 D G 1 = physicalRuled h D G 1 := by
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,s,hs,rfl⟩,rfl⟩
    exact ⟨p,hp,s,hs,by simp [firstPhysicalMap]⟩
  · rintro ⟨p,hp,s,hs,rfl⟩
    exact ⟨vec3 s (p 0+s*G p 0) (p 1+s*G p 1),
      ⟨p,hp,s,hs,by simp⟩,rfl⟩

/-- Nilpotent approximation, with finite oriented square tiles and both exact
Euclidean physical realizations. Smoothness is more than the C1 producer needs. -/
theorem nilpotent : NilpotentStatement := by
  intro D G hD hG hnil h eps hh heps
  obtain ⟨U,hU,hDU,hG⟩ := hG
  have hG1 : SmoothNear 1 D G := ⟨U,hU,hDU,hG.of_le (by norm_num)⟩
  obtain ⟨n,C,hC,hcov,hcost⟩ := nilpotent_physical_cover hh hD hG1 hnil (mul_pos hh heps)
  choose T g hT hCT using hC
  refine ⟨n,T,g,hT,?_,?_,?_⟩
  · intro z hz
    have hz' : firstPhysicalMap h z ∈ physicalRuled h D G 1 := by
      rw [← firstPhysicalMap_ruled]
      exact mem_image_of_mem _ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hz')
    rw [hCT i,projectedCylinder_carrier] at hi
    obtain ⟨x,hx,hx'⟩ := hi
    have he : x = z := firstPhysicalMap_injective hh.ne' hx'
    exact mem_iUnion.mpr ⟨i, he ▸ hx⟩
  · simp_rw [familyArea,hCT,projectedCylinder_area hh] at hcost
    have he : (∑ i, h * volume.real (T i) * physicalWeight h (g i)) =
        h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hcost
    nlinarith
  · intro a
    let C₁ : Fin n → Cylinder := fun i => projectedCylinder h (g i) (T i)
    let C₂ : Fin n → Cylinder := fun i =>
      ((C₁ i).rotate swapReflect).translate (vec3 0 0 (h*a))
    refine ⟨C₁,C₂,fun i => ?_⟩
    have hP : (C₁ i).parallelogram := projectedCylinder_parallelogram hh _ (hT i).parallelogram
    refine ⟨hP,Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram hP swapReflect) _,
      projectedCylinder_carrier h _ _,?_,projectedCylinder_area hh _ _,?_⟩
    · dsimp only [C₂]
      rw [Cylinder.translate_carrier,Cylinder.rotate_carrier,projectedCylinder_carrier,
        ← image_comp,← image_comp]
      congr 1
      funext z
      exact (physicalMaps_relation h a z).symm
    · dsimp only [C₂]
      rw [Cylinder.translate_area,Cylinder.rotate_area]
      exact projectedCylinder_area hh _ _

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_parameter_bounds {p gamma : ℝ} (hp : 1 < p)
    (hp' : p < (Real.sqrt 51-5)/2) (hg : 1 < gamma) (hg' : gamma < 1/(2-p)) :
    p < 2 ∧ 0 < 1+gamma*(p-2) ∧ 0 < 2*gamma-2 ∧ singularCoefficient p < 0 := by
  have hs : (Real.sqrt 51)^2 = (51:ℝ) := Real.sq_sqrt (by norm_num)
  have hsn := Real.sqrt_nonneg (51:ℝ)
  have hs9 : Real.sqrt 51 < 9 := by nlinarith
  have hp2 : p < 2 := by linarith
  have hgam : gamma*(2-p) < 1 := (lt_div_iff₀ (sub_pos.mpr hp2)).mp hg'
  have hroot : 2*p+5 < Real.sqrt 51 := by linarith
  have hnum : 2*p^2+10*p-13 < 0 := by nlinarith
  refine ⟨hp2, by nlinarith, by linarith, ?_⟩
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hnum) (by linarith)

lemma singularField_contDiffAt (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (singularField p) z := by
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun b : Plane => ((1/2:ℝ)/2)*(b 1/(1/2))^(p-1)*
        (p+(2-p)*(b 0/b 1)^2)) z
    have h1 : ContDiffAt ℝ ∞ (fun b : Plane => b 1/(1/2:ℝ)) z := by fun_prop
    have hpow := h1.rpow_const_of_ne (p := p-1) (by positivity)
    exact (contDiffAt_const.mul hpow).mul
      (contDiffAt_const.add (contDiffAt_const.mul (((by fun_prop :
        ContDiffAt ℝ ∞ (fun b : Plane => b 0) z).div (by fun_prop) hz.ne').pow 2)))
  · change ContDiffAt ℝ ∞ (fun b : Plane => (b 1/(1/2:ℝ))^(p-2)*b 0) z
    have h1 : ContDiffAt ℝ ∞ (fun b : Plane => b 1/(1/2:ℝ)) z := by fun_prop
    exact (h1.rpow_const_of_ne (p := p-2) (by positivity)).mul (by fun_prop)

lemma singularField_contDiffOn (p : ℝ) :
    ContDiffOn ℝ ∞ (singularField p) {z : Plane | 0 < z 1} :=
  fun _ hz => (singularField_contDiffAt p hz).contDiffWithinAt

lemma singularField_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    singularField p (r • z) = r^(p-1) • singularField p z := by
  have he : (r*z 1)/(1/2:ℝ) = r*(z 1/(1/2)) := by ring
  have hpow : r^(p-1) = r^(p-2)*r := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one hr.ne']
  ext i
  fin_cases i
  · change ((1/2:ℝ)/2)*((r*z 1)/(1/2))^(p-1)*(p+(2-p)*(r*z 0/(r*z 1))^2) =
      r^(p-1)*(((1/2:ℝ)/2)*(z 1/(1/2))^(p-1)*(p+(2-p)*(z 0/z 1)^2))
    rw [he,Real.mul_rpow hr.le (by positivity),mul_div_mul_left _ _ hr.ne']
    ring
  · change ((r*z 1)/(1/2:ℝ))^(p-2)*(r*z 0) = r^(p-1)*((z 1/(1/2))^(p-2)*z 0)
    rw [he,Real.mul_rpow hr.le (by positivity),hpow]
    ring

lemma singularField_fderiv_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (singularField p) (r • z) = r^(p-2) • fderiv ℝ (singularField p) z := by
  have he : (fun w : Plane => singularField p (r • w)) =ᶠ[𝓝 z]
      (fun w : Plane => r^(p-1) • singularField p w) := by
    filter_upwards [(isOpen_lt continuous_const (by fun_prop : Continuous (fun w : Plane => w 1))).mem_nhds hz]
      with w hw
    exact singularField_smul p hr hw
  have hd := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  have he' := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_smul r, fderiv_fun_const_smul hd] at he'
  have hp : r^(p-1) = r*r^(p-2) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one hr.ne']
    ring
  rw [hp,mul_smul] at he'
  exact (smul_right_injective (Plane →L[ℝ] Plane) hr.ne') he'

lemma singularField_level (p b : ℝ) :
    singularField p (vec2 b (1/2)) = vec2 (p/4+(2-p)*b^2) b := by
  ext i
  fin_cases i <;> simp [singularField,vec2]; ring

lemma singularField_wall (p : ℝ) {b r : ℝ} (hr : 0 < r) :
    singularField p (vec2 b r) 1 + singularField p (vec2 b r) 0 =
      (r+b)/2*(r/(1/2:ℝ))^(p-2)*((2-p)*b/r+p) ∧
    singularField p (vec2 b r) 1 - singularField p (vec2 b r) 0 =
      (r-b)/2*(r/(1/2:ℝ))^(p-2)*((2-p)*b/r-p) := by
  have hp : (r/(1/2:ℝ))^(p-1) = (r/(1/2:ℝ))^(p-2)*(r/(1/2)) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one (by positivity : r/(1/2:ℝ)≠0)]
  simp only [singularField,vec2_apply_one,vec2_apply_zero,hp]
  constructor <;> field_simp <;> ring

lemma hasFDerivAt_vec2 {f g : Plane → ℝ} {f' g' : Plane →L[ℝ] ℝ} {z : Plane}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => vec2 (f w) (g w))
      (f'.smulRight (vec2 1 0) + g'.smulRight (vec2 0 1)) z := by
  have he : (fun w => vec2 (f w) (g w)) =
      (fun w => f w • vec2 1 0 + g w • vec2 0 1) := by
    funext w
    ext i
    fin_cases i <;> simp [vec2]
  rw [he]
  exact (hf.smul_const (vec2 1 0)).add (hg.smul_const (vec2 0 1))

lemma singularField_fderiv (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (singularField p) z =
      matrixCLM ((2-p)*(z 1/(1/2:ℝ))^(p-2)*(z 0/z 1))
        ((z 1/(1/2:ℝ))^(p-2)/2*(p*(p-1)+(2-p)*(p-3)*(z 0/z 1)^2))
        ((z 1/(1/2:ℝ))^(p-2)) ((p-2)*(z 1/(1/2:ℝ))^(p-2)*(z 0/z 1)) := by
  let b : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let r : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hb := b.hasFDerivAt (x := z)
  have hr := r.hasFDerivAt (x := z)
  have hri := (hasDerivAt_inv hz.ne').comp_hasFDerivAt z hr
  have hquot := hb.mul hri
  have hscale := hr.const_mul 2
  have hpow1 := hscale.rpow_const (p := p-1) (Or.inl (by change 2*z 1 ≠ 0; positivity))
  have hpow2 := hscale.rpow_const (p := p-2) (Or.inl (by change 2*z 1 ≠ 0; positivity))
  have hP := (hpow1.const_mul ((1/2:ℝ)/2)).mul
    (((hquot.pow 2).const_mul (2-p)).const_add p)
  have hQ := hpow2.mul hb
  have hf := (hasFDerivAt_vec2 hP hQ).fderiv
  have he : (fun w : Plane => vec2 (((1/2:ℝ)/2)*(2*r w)^(p-1)*
      (p+(2-p)*(b w*(r w)⁻¹)^2)) ((2*r w)^(p-2)*b w)) = singularField p := by
    funext w
    ext i
    fin_cases i <;> simp [singularField,vec2,b,r,div_eq_mul_inv,mul_comm]
  change fderiv ℝ (fun w : Plane => vec2 (((1/2:ℝ)/2)*(2*r w)^(p-1)*
      (p+(2-p)*(b w*(r w)⁻¹)^2)) ((2*r w)^(p-2)*b w)) z = _ at hf
  rw [he] at hf
  rw [hf]
  have h2 : 0 < 2*z 1 := by positivity
  have hp1 : (2*z 1)^(p-1-1) = (2*z 1)^(p-2) := by congr 1; ring
  have hp2 : (2*z 1)^(p-2-1) = (2*z 1)^(p-2)/(2*z 1) := by
    rw [Real.rpow_sub_one h2.ne']
  have hp3 : (2*z 1)^(p-1) = (2*z 1)^(p-2)*(2*z 1) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one h2.ne']
  ext w i
  fin_cases i <;>
    simp [matrixCLM,b,r,ContinuousLinearMap.smulRight_apply,vec2,hp1,hp2,hp3] <;>
    (rw [show z 1*2=2*z 1 by ring]; field_simp [hz.ne'] <;> ring)

lemma matrixCLM_trace (a b c d : ℝ) :
    LinearMap.trace ℝ Plane (matrixCLM a b c d).toLinearMap = a+d := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr,matrixCLM_apply]

lemma matrixCLM_det (a b c d : ℝ) :
    LinearMap.det (matrixCLM a b c d).toLinearMap = a*d-b*c := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr,matrixCLM_apply]

lemma singularField_trace_det (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (singularField p) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap =
      ((z 1/(1/2:ℝ))^(p-2))^2*(p-1)/2*((2-p)*(z 0/z 1)^2-p) := by
  rw [singularField_fderiv p hz,matrixCLM_trace,matrixCLM_det]
  constructor <;> ring

lemma singularField_hyperbolic {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (singularField p) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap < 0 := by
  obtain ⟨ht,hd⟩ := singularField_trace_det p hz
  refine ⟨ht,?_⟩
  rw [hd]
  have hq : |z 0/z 1| ≤ 1 := by
    rw [abs_div,abs_of_pos hz,div_le_one hz]
    exact hb
  have hq2 : (z 0/z 1)^2 ≤ 1 := by
    have := mul_self_le_mul_self (abs_nonneg (z 0/z 1)) hq
    nlinarith [sq_abs (z 0/z 1)]
  apply mul_neg_of_pos_of_neg
  · exact div_pos (mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _)) (by linarith)) (by norm_num)
  · have := mul_le_mul_of_nonneg_left hq2 (sub_nonneg.mpr hp2.le)
    nlinarith

lemma singularField_scaled_hyperbolic {p c : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hc : c ≠ 0) {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1)
    (hd : |c| *‖fderiv ℝ (singularField p) z‖ < 1) :
    HyperbolicAt 1 (fun w => c • singularField p w) z := by
  have hdiff := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  rw [HyperbolicAt,fderiv_fun_const_smul hdiff]
  have htd := singularField_hyperbolic hp hp2 hz hb
  have heig := plane_hyperbolic_eigenvalues _ htd.1 htd.2
  let lam := Real.sqrt (-LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap)
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by linarith [htd.2])
  have hnorm : lam ≤ ‖fderiv ℝ (singularField p) z‖ := eigenvalue_le_norm _ hlam.le heig.1
  have hnonneg : 0 < |c| := abs_pos.mpr hc
  refine ⟨|c| *lam,by simpa using mul_pos hnonneg hlam,?_,?_,?_⟩
  · simpa using (mul_le_mul_of_nonneg_left hnorm hnonneg.le).trans_lt hd
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using eigenvalue_smul _ heig.1 c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using eigenvalue_smul _ heig.2 c
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using eigenvalue_smul _ heig.2 c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using eigenvalue_smul _ heig.1 c

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_norm_sq (z : Plane) : ‖z‖^2 = z 0^2+z 1^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs]

lemma plane_coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := plane_norm_sq z
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  nlinarith [sq_abs (z 0),sq_abs (z 1)]

lemma singularField_homogeneous_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) := by
  let S : Set Plane := (fun b : ℝ => vec2 b 1) '' Icc (-2 : ℝ) 2
  have hS : IsCompact S := isCompact_Icc.image (by unfold vec2; fun_prop)
  have hpos : ∀ z ∈ S, 0 < z 1 := by
    rintro z ⟨b,hb,rfl⟩
    norm_num [vec2]
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (singularField_contDiffAt p (hpos z hz)).continuousAt.continuousWithinAt)
  obtain ⟨C₂,hC₂⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((singularField_contDiffAt p (hpos z hz)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt)
  refine ⟨max 1 (max C₁ C₂),le_max_left _ _,?_⟩
  intro z hz hcone
  let u := vec2 (z 0/z 1) 1
  have hu : u ∈ S := by
    refine ⟨z 0/z 1,?_,rfl⟩
    have ht : |z 0/z 1| ≤ 2 := by
      rw [abs_div,abs_of_pos hz,div_le_iff₀ hz]
      exact hcone
    exact abs_le.mp ht
  have hue : z 1 • u = z := by
    ext i
    fin_cases i <;> simp [u,vec2]
    field_simp
  have hf := singularField_smul p hz (z := u) (by norm_num [u,vec2])
  have hd := singularField_fderiv_smul p hz (z := u) (by norm_num [u,vec2])
  rw [hue] at hf hd
  constructor
  · rw [hf,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
    calc
      _ ≤ (z 1)^(p-1)*C₁ := mul_le_mul_of_nonneg_left (hC₁ u hu) (by positivity)
      _ ≤ (z 1)^(p-1)*max 1 (max C₁ C₂) := mul_le_mul_of_nonneg_left
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
      _ = _ := mul_comm _ _
  · rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
    calc
      _ ≤ (z 1)^(p-2)*C₂ := mul_le_mul_of_nonneg_left (hC₂ u hu) (by positivity)
      _ ≤ (z 1)^(p-2)*max 1 (max C₁ C₂) := mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
      _ = _ := mul_comm _ _

lemma singularDomain_isCompact (p gamma c : ℝ) : IsCompact (singularDomain p gamma c) := by
  have hb : Continuous (fun z : Plane => z 0) := by fun_prop
  have hr : Continuous (fun z : Plane => z 1) := by fun_prop
  have hcap : Continuous (fun z : Plane => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ)) := by
    unfold ceilingPolynomial
    fun_prop
  have hclosed : IsClosed (singularDomain p gamma c) :=
    (isClosed_le continuous_const hr).inter ((isClosed_le hr continuous_const).inter
      ((isClosed_le hb.abs hr).inter (isClosed_le hr hcap)))
  apply (isCompact_closedBall (0 : Plane) 4).of_isClosed_subset hclosed
  intro z hz
  have hz0 : |z 0| ≤ 2 := hz.2.2.1.trans hz.2.1
  have hz1 : |z 1| ≤ 2 := (abs_of_nonneg ((abs_nonneg _).trans hz.2.2.1)).le.trans hz.2.1
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (plane_norm_le_sum z).trans (by linarith)

lemma singularDomain_smoothNear (p gamma : ℝ) {c : ℝ} (hc : 0 < c) :
    SmoothNear ∞ (singularDomain p gamma c) (singularField p) := by
  refine ⟨{z | 0 < z 1},isOpen_lt continuous_const (by fun_prop),?_,singularField_contDiffOn p⟩
  intro z hz
  exact (Real.rpow_pos_of_pos hc gamma).trans_le hz.1

lemma singular_cutoff_small {p gamma : ℝ} (hpg : 0 < 1+gamma*(p-2)) :
    Tendsto (fun c : ℝ => c*(c^gamma)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^(1+gamma*(p-2))) (𝓝[>] 0)
      (𝓝 ((0:ℝ)^(1+gamma*(p-2)))) :=
    ((Real.continuous_rpow_const hpg.le).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hpg.ne'] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc : 0 < c := hc
  rw [← Real.rpow_mul hc.le,Real.rpow_add hc,Real.rpow_one]

lemma singular_tip_small {gamma : ℝ} (hg : 1 < gamma) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) (fun c : ℝ => (c^gamma)^2) (fun c => c^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h : Tendsto (fun c : ℝ => c^(2*gamma-2)) (𝓝[>] 0)
        (𝓝 ((0:ℝ)^(2*gamma-2))) :=
      ((Real.continuous_rpow_const (show 0 ≤ 2*gamma-2 by linarith)).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow (by linarith : 2*gamma-2 ≠ 0)] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc : 0 < c := hc
    rw [← Real.rpow_natCast,← Real.rpow_mul hc.le,← Real.rpow_natCast,← Real.rpow_sub hc]
    congr 1
    ring
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((ne_of_gt (pow_pos hc 2)) h)

lemma vec2_coordinates (z : Plane) : vec2 (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> rfl

lemma singular_wall_coefficient_bound (p : ℝ) {z : Plane}
    (hz : 0 < z 1) (hb : |z 0| ≤ 2*z 1) {e : ℝ} (he : |e| ≤ 1) :
    |(z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)| ≤
      ((2:ℝ)^(p-2)/2*(2*|2-p|+|p|))*(z 1)^(p-2) := by
  have hq : |z 0/z 1| ≤ 2 := by
    rw [abs_div,abs_of_pos hz,div_le_iff₀ hz]
    exact hb
  have ha : |(2-p)*(z 0/z 1)+e*p| ≤ 2*|2-p|+|p| := by
    calc
      _ ≤ |(2-p)*(z 0/z 1)|+|e*p| := abs_add_le _ _
      _ = |2-p| *|z 0/z 1|+|e| *|p| := by rw [abs_mul,abs_mul]
      _ ≤ |2-p| *2+1*|p| := add_le_add
        (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
        (mul_le_mul_of_nonneg_right he (abs_nonneg _))
      _ = _ := by ring
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (z 1/(1/2:ℝ))^(p-2)/2)]
  calc
    _ ≤ (z 1/(1/2:ℝ))^(p-2)/2*(2*|2-p|+|p|) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by
      rw [show z 1/(1/2:ℝ)=2*z 1 by ring,Real.mul_rpow (by norm_num) hz.le]
      ring

lemma singular_uniform_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) ∧
      ∀ e : ℝ, |e| ≤ 1 → |(z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)| ≤
        C*(z 1)^(p-2) := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  let W := (2:ℝ)^(p-2)/2*(2*|2-p|+|p|)
  refine ⟨max C W,hC.trans (le_max_left _ _),?_⟩
  intro z hz hb
  obtain ⟨h0,h1⟩ := hbound z hz hb
  refine ⟨h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),?_⟩
  intro e he
  exact (singular_wall_coefficient_bound p hz hb he).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_ConeVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma coneTriangle_isCompact (a : ℝ) : IsCompact (coneTriangle a) := by
  have hc : IsClosed (coneTriangle a) := by
    unfold coneTriangle
    exact (isClosed_le (f := fun _ : Plane => (0:ℝ)) (g := fun z => z 1) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => a) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1) (by fun_prop) (by fun_prop)))
  exact (isCompact_closedBall (0:Plane) (2*a)).of_isClosed_subset hc (by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have he := plane_norm_le_sum z
    rw [abs_of_nonneg hz.1] at he
    exact he.trans (by linarith [hz.2.1,hz.2.2]))

lemma coneTriangle_volume {a : ℝ} (ha : 0 ≤ a) : volume.real (coneTriangle a) = a^2 := by
  have heq : ∀ z : Plane, z ∈ coneTriangle a ↔ z 1 ∈ Icc 0 a ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneTriangle,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_volume_horizontal_interval (coneTriangle_isCompact a).measurableSet
    (coneTriangle_isCompact a).measure_lt_top.ne (s := Icc 0 a) (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc (0:ℝ) a, max (r- -r) 0) = ∫ r in (0:ℝ)..a, 2*r := by
    rw [intervalIntegral.integral_of_le ha,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change max (r- -r) 0 = 2*r
    rw [max_eq_left (by linarith [hr.1])]
    ring
  change (∫ r in Icc (0:ℝ) a, max (r- -r) 0) = a^2
  rw [he,intervalIntegral.integral_const_mul]
  have hh := integral_pow (a := (0:ℝ)) (b := a) 1
  simp only [pow_one] at hh
  rw [hh]
  norm_num
  ring

lemma coneBand_isCompact (d a : ℝ) : IsCompact (coneBand d a) := by
  apply (coneTriangle_isCompact a).of_isClosed_subset
  · unfold coneBand
    exact (isClosed_le (f := fun _ : Plane => d) (g := fun z => z 1) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => a) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1) (by fun_prop) (by fun_prop)))
  · intro z hz
    exact ⟨(abs_nonneg _).trans hz.2.2,hz.2⟩

lemma coneBand_volume {d a : ℝ} (hd : 0 ≤ d) (hda : d ≤ a) :
    volume.real (coneBand d a) = a^2-d^2 := by
  have heq : ∀ z : Plane, z ∈ coneBand d a ↔ z 1 ∈ Icc d a ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneBand,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_volume_horizontal_interval (coneBand_isCompact d a).measurableSet
    (coneBand_isCompact d a).measure_lt_top.ne (s := Icc d a) (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc d a, max (r- -r) 0) = ∫ r in d..a, 2*r := by
    rw [intervalIntegral.integral_of_le hda,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change max (r- -r) 0 = 2*r
    rw [max_eq_left (by linarith [hr.1])]
    ring
  change (∫ r in Icc d a, max (r- -r) 0) = a^2-d^2
  rw [he,intervalIntegral.integral_const_mul]
  have hh := integral_pow (a := d) (b := a) 1
  simp only [pow_one] at hh
  rw [hh]
  norm_num
  ring

lemma coneBand_volume_vertical {d a : ℝ} (ha : a ≤ 2) :
    volume.real (coneBand d a) = ∫ b in Icc (-2:ℝ) 2, max (a-max d |b|) 0 := by
  apply plane_volume_vertical_interval (coneBand_isCompact d a).measurableSet
    (coneBand_isCompact d a).measure_lt_top.ne measurableSet_Icc
  intro z
  change (d ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1) ↔
    z 0 ∈ Icc (-2:ℝ) 2 ∧ z 1 ∈ Icc (max d |z 0|) a
  simp only [mem_Icc,max_le_iff]
  constructor
  · intro hz
    have hb := abs_le.mp (hz.2.2.trans (hz.2.1.trans ha))
    exact ⟨hb,⟨⟨hz.1,hz.2.2⟩,hz.2.1⟩⟩
  · rintro ⟨_,⟨⟨hd,hb⟩,ha⟩⟩
    exact ⟨hd,ha,hb⟩

lemma singularDomain_volume_vertical (p gamma c : ℝ)
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2) :
    volume.real (singularDomain p gamma c) = ∫ b in Icc (-2:ℝ) 2,
      max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-max (c^gamma) |b|) 0 := by
  apply plane_volume_vertical_interval (singularDomain_isCompact p gamma c).measurableSet
    (singularDomain_isCompact p gamma c).measure_lt_top.ne measurableSet_Icc
  intro z
  unfold singularDomain
  simp only [mem_ofPred_eq,mem_Icc,max_le_iff]
  constructor
  · intro hz
    have hb := abs_le.mp (hz.2.2.1.trans hz.2.1)
    exact ⟨hb,⟨⟨hz.1,hz.2.2.1⟩,hz.2.2.2⟩⟩
  · rintro ⟨hb,⟨⟨hd,hb'⟩,hceil⟩⟩
    exact ⟨hd,hceil.trans (hcap (z 0) (abs_le.mpr hb)),hb',hceil⟩

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_TipCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsTriangle.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsTriangle P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsTriangle (f '' P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  refine ⟨f c,f u,f v,?_,?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : f ∘ ![u,v] = ![f u,f v] := by funext i; fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨_,⟨s,t,hs,ht,hst,rfl⟩,rfl⟩
      exact ⟨s,t,hs,ht,hst,by simp⟩
    · rintro ⟨s,t,hs,ht,hst,rfl⟩
      exact ⟨c+s•u+t•v,⟨s,t,hs,ht,hst,rfl⟩,by simp⟩

lemma IsTriangle.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsTriangle P) (a : E) :
    IsTriangle ((fun x => a+x) '' P) := by
  obtain ⟨c,u,v,hli,rfl⟩ := hP
  refine ⟨a+c,u,v,hli,?_⟩
  ext x
  constructor
  · rintro ⟨_,⟨s,t,hs,ht,hst,rfl⟩,rfl⟩
    exact ⟨s,t,hs,ht,hst,by abel_nf⟩
  · rintro ⟨s,t,hs,ht,hst,rfl⟩
    exact ⟨c+s•u+t•v,⟨s,t,hs,ht,hst,rfl⟩,by abel_nf⟩

lemma Cylinder.rotate_triangle {C : Cylinder} (hC : C.triangle)
    (R : Space ≃ₗᵢ[ℝ] Space) : (C.rotate R).triangle :=
  hC.linear_image (rotatedPlane C.axis R).toLinearMap (rotatedPlane C.axis R).injective

lemma Cylinder.translate_triangle {C : Cylinder} (hC : C.triangle) (q : Space) :
    (C.translate q).triangle := hC.translate (C.transversePart q)

lemma coneTriangle_triangle {a : ℝ} (ha : 0 < a) : IsTriangle (coneTriangle a) := by
  refine ⟨0,vec2 a a,vec2 (-a) a,?_,?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t he
    have h0 := congrArg (fun z : Plane => z 0) he
    have h1 := congrArg (fun z : Plane => z 1) he
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,vec2_apply_zero,vec2_apply_one,
      PiLp.zero_apply] at h0 h1
    constructor
    · exact (mul_eq_zero.mp (by linarith : s*a=0)).resolve_right ha.ne'
    · exact (mul_eq_zero.mp (by linarith : t*a=0)).resolve_right ha.ne'
  · ext z
    constructor
    · intro hz
      have hab := abs_le.mp hz.2.2
      refine ⟨(z 1+z 0)/(2*a),(z 1-z 0)/(2*a),
        div_nonneg (by linarith [hab.1]) (by positivity),
        div_nonneg (by linarith [hab.2]) (by positivity),?_,?_⟩
      · rw [← add_div,div_le_one (by positivity : 0 < 2*a)]
        linarith [hz.2.1]
      · ext i
        fin_cases i <;> simp [vec2] <;> field_simp <;> ring
    · rintro ⟨s,t,hs,ht,hst,rfl⟩
      simp only [coneTriangle,mem_ofPred_eq,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
        vec2_apply_one,vec2_apply_zero,zero_add]
      refine ⟨by positivity,by nlinarith,abs_le.mpr ⟨by nlinarith,by nlinarith⟩⟩

lemma lowerTipCylinder_triangle {d : ℝ} (hd : 0 < d) : (lowerTipCylinder d).triangle :=
  (coneTriangle_triangle (by positivity : 0 < 2*d)).linear_image _
    (perpendicularProjection_injective (Real.sqrt_pos.mpr (by norm_num)) 0)

lemma upperTipCylinder_triangle {d : ℝ} (hd : 0 < d) : (upperTipCylinder d).triangle :=
  Cylinder.translate_triangle (Cylinder.rotate_triangle (lowerTipCylinder_triangle hd) swapReflect) _

lemma lowerTipCylinder_area {d : ℝ} (hd : 0 ≤ d) :
    (lowerTipCylinder d).area = 4*Real.sqrt 2*d^2 := by
  rw [lowerTipCylinder,projectedCylinder_area (Real.sqrt_pos.mpr (by norm_num)),
    coneTriangle_volume (by positivity : 0 ≤ 2*d)]
  simp only [physicalWeight,PiLp.zero_apply,zero_pow (by norm_num : 2 ≠ 0),add_zero,
    mul_zero,Real.sqrt_one,div_one,mul_one]
  ring

lemma upperTipCylinder_area {d : ℝ} (hd : 0 ≤ d) :
    (upperTipCylinder d).area = 4*Real.sqrt 2*d^2 := by
  rw [upperTipCylinder,Cylinder.translate_area,Cylinder.rotate_area,lowerTipCylinder_area hd]

lemma lowerTipCylinder_carrier (d : ℝ) : (lowerTipCylinder d).carrier = lowerTip d := by
  ext z
  rw [lowerTipCylinder,projectedCylinder_mem_iff]
  constructor
  · rintro ⟨b,hb,s,rfl⟩
    exact ⟨b 1,hb.1,hb.2.1,by simpa [planeEmbedding,physicalDirection,vec3] using hb.2.2,
      by simp [planeEmbedding,physicalDirection,vec3]⟩
  · rintro ⟨t,ht0,htd,hy,hz⟩
    refine ⟨vec2 (z 1) t,⟨ht0,htd,hy⟩,z 0,?_⟩
    ext i
    fin_cases i <;> simp [planeEmbedding,physicalDirection,vec3,hz]

lemma upperTip_image (d : ℝ) :
    (fun z => vec3 0 0 (Real.sqrt 2)+z) '' (swapReflect '' lowerTip d) = upperTip d := by
  ext z
  constructor
  · rintro ⟨_,⟨w,⟨t,ht0,htd,hy,hz⟩,rfl⟩,rfl⟩
    refine ⟨t,ht0,htd,by simpa [swapReflect,vec3] using hy,?_⟩
    change Real.sqrt 2 + -(w 2) = Real.sqrt 2*(1-t)
    rw [hz]
    ring
  · rintro ⟨t,ht0,htd,hx,hz⟩
    refine ⟨swapReflect (vec3 (z 1) (z 0) (Real.sqrt 2*t)),
      ⟨vec3 (z 1) (z 0) (Real.sqrt 2*t),⟨t,ht0,htd,hx,rfl⟩,rfl⟩,?_⟩
    ext i
    fin_cases i <;> simp [swapReflect,vec3,hz]
    ring

lemma upperTipCylinder_carrier (d : ℝ) : (upperTipCylinder d).carrier = upperTip d := by
  rw [upperTipCylinder,Cylinder.translate_carrier,Cylinder.rotate_carrier,lowerTipCylinder_carrier,
    upperTip_image]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma inverse_in_closedBall {V : Plane → Plane} {q : Plane} {R k : ℝ} (hR : 0 ≤ R)
    (hcont : ∀ z ∈ Metric.closedBall q R, DifferentiableAt ℝ V z)
    (hsize : ∀ z ∈ Metric.closedBall q R, |k| *‖V z‖ ≤ R)
    (hder : ∀ z ∈ Metric.closedBall q R, |k| *‖fderiv ℝ V z‖ ≤ 1/2) :
    ∃ z ∈ Metric.closedBall q R, q = z+k • V z := by
  let S := Metric.closedBall q R
  let F : S → S := fun z => ⟨q-k • V z,by
    rw [Metric.mem_closedBall,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs]
    exact hsize z z.2⟩
  have hL : ContractingWith (1/2 : NNReal) F := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => k • V z) (C := 1/2)
      (fun z hz => (hcont z hz).const_smul k)
      (fun z hz => by
        rw [fderiv_fun_const_smul (hcont z hz),norm_smul,Real.norm_eq_abs]
        exact hder z hz)
      (convex_closedBall q R) y.2 x.2
    change ‖(q-k • V x)-(q-k • V y)‖ ≤ (1/2)*‖(x:Plane)-(y:Plane)‖
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
    exact he
  have : Nonempty S := ⟨⟨q,Metric.mem_closedBall_self hR⟩⟩
  have : IsClosed S := Metric.isClosed_closedBall
  let z := ContractingWith.fixedPoint F hL
  have hz := congrArg Subtype.val hL.fixedPoint_isFixedPt
  refine ⟨z,z.2,?_⟩
  change q-k • V z = z at hz
  exact (sub_eq_iff_eq_add.mp hz)

lemma singular_inverse_small {p : ℝ} (hp2 : p < 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d c B T k : ℝ), 0 < d → 0 ≤ c →
      c*C*d^(p-2) ≤ 1/8 → 2*d ≤ T → T ≤ 1 → |B| ≤ T → |k| ≤ c →
      ∃ z : Plane, d ≤ z 1 ∧ z 1 ≤ 2 ∧ |z 0| ≤ z 1 ∧
        vec2 B T = z+k • singularField p z := by
  obtain ⟨C,hC,hbound⟩ := singular_uniform_bounds p
  refine ⟨C,hC,?_⟩
  intro d c B T k hd hc hsmall hT hT1 hB hk
  have hTp : 0 < T := by linarith
  have hCp : 0 ≤ C := by linarith
  have hball : ∀ z ∈ Metric.closedBall (vec2 B T) (T/4),
      d ≤ z 1 ∧ z 1 ≤ 5*T/4 ∧ |z 0| ≤ 2*z 1 := by
    intro z hz
    rw [Metric.mem_closedBall,dist_eq_norm] at hz
    have hr := (plane_coordinate_le (z-vec2 B T) 1).trans hz
    have hb := (plane_coordinate_le (z-vec2 B T) 0).trans hz
    change |z 1-T| ≤ T/4 at hr
    change |z 0-B| ≤ T/4 at hb
    obtain ⟨hrl,hru⟩ := abs_le.mp hr
    have hb' : |z 0| ≤ T/4+T := by
      calc
        _ = |(z 0-B)+B| := by congr 1; ring
        _ ≤ |z 0-B|+|B| := abs_add_le _ _
        _ ≤ T/4+T := add_le_add hb hB
    exact ⟨by linarith,by linarith,by linarith⟩
  have hprod : ∀ z ∈ Metric.closedBall (vec2 B T) (T/4), |k| * C*(z 1)^(p-2) ≤ 1/8 := by
    intro z hz
    have hz' := hball z hz
    have hzp : 0 < z 1 := hd.trans_le hz'.1
    calc
      _ ≤ c*C*(z 1)^(p-2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hk hCp) (by positivity)
      _ ≤ c*C*d^(p-2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hd hz'.1 (by linarith)) (mul_nonneg hc hCp)
      _ ≤ _ := hsmall
  obtain ⟨z,hz,heq⟩ := inverse_in_closedBall (V := singularField p)
    (k := k) (show 0 ≤ T/4 by positivity)
    (fun z hz => (singularField_contDiffAt p (hd.trans_le (hball z hz).1)).differentiableAt (by norm_num))
    (fun z hz => by
      have hz' := hball z hz
      have hzp := hd.trans_le hz'.1
      have hV := (hbound z hzp hz'.2.2).1
      calc
        _ ≤ |k| * (C*(z 1)^(p-1)) := mul_le_mul_of_nonneg_left hV (abs_nonneg _)
        _ = (|k| * C*(z 1)^(p-2))*z 1 := by
          rw [show p-1=p-2+1 by ring,Real.rpow_add_one hzp.ne']
          ring
        _ ≤ (1/8)*z 1 := mul_le_mul_of_nonneg_right (hprod z hz) hzp.le
        _ ≤ T/4 := by linarith)
    (fun z hz => by
      have hz' := hball z hz
      have hV := (hbound z (hd.trans_le hz'.1) hz'.2.2).2.1
      exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans
        (by simpa only [mul_assoc] using hprod z hz)).trans (by norm_num))
  have hz' := hball z hz
  have hzp := hd.trans_le hz'.1
  have htheta : ∀ e : ℝ, |e| ≤ 1 →
      0 < 1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)) := by
    intro e he
    have ht := mul_le_mul_of_nonneg_left ((hbound z hzp hz'.2.2).2.2 e he) (abs_nonneg k)
    rw [← abs_mul] at ht
    have ht' : |k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p))| ≤ 1/8 := by
      exact ht.trans (by simpa only [mul_assoc] using hprod z hz)
    have := (abs_le.mp ht').1
    linarith
  have he0 := congrArg (fun w : Plane => w 0) heq
  have he1 := congrArg (fun w : Plane => w 1) heq
  change B = z 0+k*singularField p z 0 at he0
  change T = z 1+k*singularField p z 1 at he1
  have hw := singularField_wall p (b := z 0) hzp
  rw [vec2_coordinates] at hw
  have hwplus : T+B = (z 1+z 0)*(1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+1*p))) := by
    calc
      _ = z 1+z 0+k*(singularField p z 1+singularField p z 0) := by rw [he0,he1]; ring
      _ = _ := by rw [hw.1]; ring
  have hwminus : T-B = (z 1-z 0)*(1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+(-1)*p))) := by
    calc
      _ = z 1-z 0+k*(singularField p z 1-singularField p z 0) := by rw [he0,he1]; ring
      _ = _ := by rw [hw.2]; ring
  have hp0 : 0 ≤ z 1+z 0 := (mul_nonneg_iff_of_pos_right (htheta 1 (by norm_num))).mp
    (by rw [← hwplus]; linarith [(abs_le.mp hB).1])
  have hm0 : 0 ≤ z 1-z 0 := (mul_nonneg_iff_of_pos_right (htheta (-1) (by norm_num))).mp
    (by rw [← hwminus]; linarith [(abs_le.mp hB).2])
  exact ⟨z,hz'.1,by linarith [hz'.2.1],abs_le.mpr ⟨by linarith,by linarith⟩,heq⟩

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceiling_nonneg {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (b : ℝ) :
    0 ≤ ceilingPolynomial p b := by
  unfold ceilingPolynomial
  have : 0 ≤ 2-p := sub_nonneg.mpr hp2
  positivity

lemma ceiling_P_identity (p x y : ℝ) :
    ceilingPolynomial p x + ceilingPolynomial p y -
      x^2*(p/4+(2-p)*y^2)-y^2*(p/4+(2-p)*x^2) = (2-p)*(x^2-y^2)^2 := by
  unfold ceilingPolynomial
  ring

lemma singular_region_estimates (p : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Plane) (B : ℝ),
      |z 0| ≤ 2 → (1/2:ℝ) ≤ z 1 → z 1 ≤ 2 → |B| ≤ 2 →
      |singularField p z 0| ≤ K ∧
      |singularField p z 1-z 0| ≤ K*(z 1-1/2) ∧
      |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*(|z 0-B|+(z 1-1/2)) ∧
      |ceilingPolynomial p (z 0)-ceilingPolynomial p B| ≤ K*|z 0-B| := by
  let S : Set Plane := (EuclideanSpace.proj 0) ⁻¹' Icc (-2:ℝ) 2 ∩
    (EuclideanSpace.proj 1) ⁻¹' Icc (1/2:ℝ) 2
  have hSc : IsClosed S := (isClosed_Icc.preimage (by fun_prop)).inter
    (isClosed_Icc.preimage (by fun_prop))
  have hS : IsCompact S := (isCompact_closedBall (0:Plane) 4).of_isClosed_subset hSc (by
    intro z hz
    change z 0 ∈ Icc (-2:ℝ) 2 ∧ z 1 ∈ Icc (1/2:ℝ) 2 at hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have ha : |z 0| ≤ 2 := abs_le.mpr hz.1
    have hb : |z 1| ≤ 2 := (abs_of_nonneg (by linarith [hz.2.1])).le.trans hz.2.2
    exact (plane_norm_le_sum z).trans (by linarith))
  have hconv : Convex ℝ S := ((convex_Icc (-2:ℝ) 2).linear_preimage (EuclideanSpace.proj 0).toLinearMap).inter
    ((convex_Icc (1/2:ℝ) 2).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hsmooth : ∀ z ∈ S, ContDiffAt ℝ ∞ (singularField p) z := by
    intro z hz
    apply singularField_contDiffAt
    have hz1 : (1/2:ℝ) ≤ z 1 := hz.2.1
    linarith
  obtain ⟨C₀,hC₀⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (hsmooth z hz).continuousAt.continuousWithinAt)
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((hsmooth z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  have hdelta : ContDiff ℝ ∞ (ceilingPolynomial p) := by unfold ceilingPolynomial; fun_prop
  obtain ⟨C₂,hC₂⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (f := fderiv ℝ (ceilingPolynomial p))
    (fun _ _ => (hdelta.contDiffAt.continuousAt_fderiv (by norm_num)).continuousWithinAt)
  let K := max 1 (max C₀ (max C₁ C₂))
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : C₀ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK₁ : C₁ ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hK₂ : C₂ ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hKn : 0 ≤ K := by linarith
  have hlip : ∀ z ∈ S, ∀ w ∈ S, ‖singularField p z-singularField p w‖ ≤ K*‖z-w‖ := by
    intro z hz w hw
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => (hsmooth q hq).differentiableAt (by norm_num))
      (fun q hq => (hC₁ q hq).trans hK₁) hconv hw hz
  have hdlip : ∀ b ∈ Icc (-2:ℝ) 2, ∀ B ∈ Icc (-2:ℝ) 2,
      |ceilingPolynomial p b-ceilingPolynomial p B| ≤ K*|b-B| := by
    intro b hb B hB
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := ceilingPolynomial p) (fun _ _ => hdelta.differentiable (by norm_num) _)
      (fun q hq => (hC₂ q hq).trans hK₂) (convex_Icc _ _) hB hb
  refine ⟨K,hK,?_⟩
  intro z B hz0 hz1 hz2 hB
  have hz : z ∈ S := ⟨abs_le.mp hz0,⟨hz1,hz2⟩⟩
  have hw : vec2 (z 0) (1/2) ∈ S := ⟨abs_le.mp hz0,by norm_num [vec2]⟩
  have hwB : vec2 B (1/2) ∈ S := ⟨abs_le.mp hB,by norm_num [vec2]⟩
  refine ⟨(plane_coordinate_le _ 0).trans ((hC₀ z hz).trans hK₀),?_,?_,hdlip _ (abs_le.mp hz0) _ (abs_le.mp hB)⟩
  · have h := (plane_coordinate_le (singularField p z-singularField p (vec2 (z 0) (1/2))) 1).trans (hlip z hz _ hw)
    rw [singularField_level] at h
    change |singularField p z 1-z 0| ≤ K*‖z-vec2 (z 0) (1/2)‖ at h
    apply h.trans
    have he := plane_norm_le_sum (z-vec2 (z 0) (1/2))
    simpa only [PiLp.sub_apply,vec2_apply_zero,vec2_apply_one,sub_self,abs_zero,zero_add,
      abs_of_nonneg (sub_nonneg.mpr hz1)] using mul_le_mul_of_nonneg_left he hKn
  · have h := (plane_coordinate_le (singularField p z-singularField p (vec2 B (1/2))) 0).trans (hlip z hz _ hwB)
    rw [singularField_level] at h
    change |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*‖z-vec2 B (1/2)‖ at h
    apply h.trans
    have he := plane_norm_le_sum (z-vec2 B (1/2))
    simpa only [PiLp.sub_apply,vec2_apply_zero,vec2_apply_one,
      abs_of_nonneg (sub_nonneg.mpr hz1)] using mul_le_mul_of_nonneg_left he hKn

lemma abs_unit_mul_le {x A B : ℝ} (hx : |x| ≤ 1) (hA : |A| ≤ B) :
    |x*A| ≤ B := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right hx (abs_nonneg A)).trans (by simpa using hA)

lemma singular_overlap_algebra {p K c x y bm bp rm rp Pm Pp Qm Qp : ℝ}
    (hp2 : p ≤ 2) (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcK : c*K ≤ 1/2) (hcsmall : 16*K^2*c^3 ≤ 2*c^(5/2:ℝ))
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrm : 1/2 ≤ rm) (hrp : 1/2 ≤ rp)
    (hPm : |Pm| ≤ K) (hPp : |Pp| ≤ K)
    (hQm : |Qm-bm| ≤ K*(rm-1/2)) (hQp : |Qp-bp| ≤ K*(rp-1/2))
    (hPmy : |Pm-(p/4+(2-p)*y^2)| ≤ K*(|bm-y|+(rm-1/2)))
    (hPpx : |Pp-(p/4+(2-p)*x^2)| ≤ K*(|bp-x|+(rp-1/2)))
    (hdm : |ceilingPolynomial p bm-ceilingPolynomial p y| ≤ K*|bm-y|)
    (hdp : |ceilingPolynomial p bp-ceilingPolynomial p x| ≤ K*|bp-x|)
    (hbm : bm=y-c*x*Pm) (hbp : bp=x+c*y*Pp)
    (hsum : rm+rp=1+c*(y*Qp-x*Qm)) :
    rm ≤ 1/2+c^2*ceilingPolynomial p bm+c^(5/2:ℝ) ∨
    rp ≤ 1/2+c^2*ceilingPolynomial p bp+c^(5/2:ℝ) := by
  have hKn : 0 ≤ K := by linarith
  have hxs : |x^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith only [(abs_le.mp hx).1,(abs_le.mp hx).2]
  have hys : |y^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg y)]; nlinarith only [(abs_le.mp hy).1,(abs_le.mp hy).2]
  have hbm' : |bm-y| ≤ c*K := by
    rw [hbm,sub_sub_cancel_left,abs_neg,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hx hPm) hc
  have hbp' : |bp-x| ≤ c*K := by
    rw [hbp,add_sub_cancel_left,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hy hPp) hc
  let D := rm+rp-1
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hEd : |y*(Qp-bp)-x*(Qm-bm)| ≤ K*D := by
    calc
      _ ≤ |y*(Qp-bp)|+|x*(Qm-bm)| := abs_sub _ _
      _ ≤ K*(rp-1/2)+K*(rm-1/2) := add_le_add (abs_unit_mul_le hy hQp) (abs_unit_mul_le hx hQm)
      _ = _ := by dsimp [D]; ring
  have hPe : |y^2*Pp+x^2*Pm| ≤ 2*K := by
    calc
      _ ≤ |y^2*Pp|+|x^2*Pm| := abs_add_le _ _
      _ ≤ K+K := add_le_add (abs_unit_mul_le hys hPp) (abs_unit_mul_le hxs hPm)
      _ = _ := by ring
  have hDeq : D=c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := by
    dsimp [D]
    rw [hsum,hbm,hbp]
    ring
  have hDb : D ≤ 4*K*c^2 := by
    have hu : D ≤ c^2*(2*K)+c*(K*D) := by
      calc
        D = c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := hDeq
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hPe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hEd) hc)
    have hmul := mul_le_mul_of_nonneg_right hcK hD
    nlinarith only [hmul,hu]
  have hrmb : rm-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hrpb : rp-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hc2 : c^2 ≤ c := by nlinarith only [hc,hc1]
  have hPmy' : |Pm-(p/4+(2-p)*y^2)| ≤ 5*K^2*c := by
    apply hPmy.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbm' hrmb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  have hPpx' : |Pp-(p/4+(2-p)*x^2)| ≤ 5*K^2*c := by
    apply hPpx.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbp' hrpb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  let A := x^2*(p/4+(2-p)*y^2)+y^2*(p/4+(2-p)*x^2)
  have hAe : |y^2*Pp+x^2*Pm-A| ≤ 10*K^2*c := by
    calc
      _ = |y^2*(Pp-(p/4+(2-p)*x^2))+x^2*(Pm-(p/4+(2-p)*y^2))| := by dsimp [A]; congr 1; ring
      _ ≤ |y^2*(Pp-(p/4+(2-p)*x^2))|+|x^2*(Pm-(p/4+(2-p)*y^2))| := abs_add_le _ _
      _ ≤ 5*K^2*c+5*K^2*c := add_le_add (abs_unit_mul_le hys hPpx') (abs_unit_mul_le hxs hPmy')
      _ = _ := by ring
  have hDelta : D ≤ c^2*A+14*K^2*c^3 := by
    have hh : D-c^2*A ≤ c^2*(10*K^2*c)+c*(K*(4*K*c^2)) := by
      calc
        _ = c^2*(y^2*Pp+x^2*Pm-A)+c*(y*(Qp-bp)-x*(Qm-bm)) := by rw [hDeq]; ring
        _ ≤ c^2*(10*K^2*c)+c*(K*D) := add_le_add
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hAe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hEd) hc)
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDb hKn) hc)
    nlinarith only [hh]
  have hdm' : ceilingPolynomial p y-K^2*c ≤ ceilingPolynomial p bm := by
    have hh := hdm.trans (mul_le_mul_of_nonneg_left hbm' hKn)
    have hh' := (abs_le.mp hh).1
    nlinarith only [hh']
  have hdp' : ceilingPolynomial p x-K^2*c ≤ ceilingPolynomial p bp := by
    have hh := hdp.trans (mul_le_mul_of_nonneg_left hbp' hKn)
    have hh' := (abs_le.mp hh).1
    nlinarith only [hh']
  have hAid : A ≤ ceilingPolynomial p y+ceilingPolynomial p x := by
    have hh := ceiling_P_identity p x y
    have hz : 0 ≤ (2-p)*(x^2-y^2)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    dsimp [A]
    linarith
  by_contra h
  push Not at h
  have hfail : c^2*(ceilingPolynomial p bm+ceilingPolynomial p bp)+2*c^(5/2:ℝ) < D := by
    dsimp [D]
    linarith [h.1,h.2]
  have hdlow : A-2*K^2*c ≤ ceilingPolynomial p bm+ceilingPolynomial p bp := by linarith
  have hh := mul_le_mul_of_nonneg_left hdlow (sq_nonneg c)
  nlinarith only [hh,hfail,hDelta,hcsmall]

lemma singular_overlap_small {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c x y : ℝ) (zm zp : Plane),
      0 ≤ c → c ≤ 1 → c*K ≤ 1/2 → 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) →
      |x| ≤ 1 → |y| ≤ 1 → zm 1 ≤ 2 → zp 1 ≤ 2 →
      |zm 0| ≤ zm 1 → |zp 0| ≤ zp 1 →
      zm 0=y-c*x*singularField p zm 0 → zp 0=x+c*y*singularField p zp 0 →
      zm 1+zp 1=1+c*(y*singularField p zp 1-x*singularField p zm 1) →
      zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) ∨
      zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by
  obtain ⟨K,hK,he⟩ := singular_region_estimates p
  refine ⟨K,hK,?_⟩
  intro c x y zm zp hc hc1 hcK hsmall hx hy hzm hzp hbzm hbzp hezm hezp hesum
  by_cases hm : zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ)
  · exact Or.inl hm
  by_cases hp' : zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ)
  · exact Or.inr hp'
  have hrm : 1/2 ≤ zm 1 := by
    have hn := ceiling_nonneg hp hp2 (zm 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) := by positivity
    linarith
  have hrp : 1/2 ≤ zp 1 := by
    have hn := ceiling_nonneg hp hp2 (zp 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by positivity
    linarith
  obtain ⟨hPm,hQm,hPmy,hdm⟩ := he zm y (hbzm.trans hzm) hrm hzm (hy.trans (by norm_num))
  obtain ⟨hPp,hQp,hPpx,hdp⟩ := he zp x (hbzp.trans hzp) hrp hzp (hx.trans (by norm_num))
  exact singular_overlap_algebra hp2 hK hc hc1 hcK hsmall hx hy hrm hrp
    hPm hPp hQm hQp hPmy hPpx hdm hdp hezm hezp hesum

lemma right_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 ((0:ℝ)^q)) :=
    ((Real.continuous_rpow_const hq.le).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq.ne'] using h

lemma overlap_error_eventually (K : ℝ) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) := by
  have h : Tendsto (fun c : ℝ => 16*K^2*c^(1/2:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (right_rpow_tendsto_zero (q := (1/2:ℝ)) (by norm_num)).const_mul (16*K^2)
  filter_upwards [self_mem_nhdsWithin,h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<2))] with c hc hb
  have hc : 0 < c := hc
  have he : c^3=c^(1/2:ℝ)*c^(5/2:ℝ) := by
    rw [← Real.rpow_add hc]
    norm_num
  rw [he]
  nlinarith only [mul_le_mul_of_nonneg_right hb.le (Real.rpow_nonneg hc.le (5/2:ℝ))]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_CapAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma positivepart_increment {a h t : ℝ} (hh : 0 ≤ h) :
    0 ≤ max (a+h-t) 0-max (a-t) 0 ∧ max (a+h-t) 0-max (a-t) 0 ≤ h := by
  by_cases ht : t ≤ a
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
    constructor <;> linarith
  · rw [show max (a-t) 0 = 0 from max_eq_right (by linarith), sub_zero]
    exact ⟨le_max_right _ _, max_le (by linarith) hh⟩

lemma positivepart_floor_increment {a d h t : ℝ} (hd : d ≤ a) (hh : 0 ≤ h) :
    max (a+h-max d t) 0-max (a-max d t) 0 = max (a+h-t) 0-max (a-t) 0 := by
  by_cases ht : t ≤ d
  · rw [max_eq_left ht,max_eq_left (by linarith),max_eq_left (by linarith),
      max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge ht)]

lemma rpow_five_halves_div_square {c : ℝ} (hc : 0 < c) :
    c^(5/2:ℝ)/c^2=c^(1/2:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_sub hc]
  norm_num

lemma capIncrementQuotient_nonneg_bound {p c b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hc : 0 < c) :
    0 ≤ capIncrementQuotient p c b ∧
      capIncrementQuotient p c b ≤ ceilingPolynomial p b+c^(1/2:ℝ) := by
  have hd := ceiling_nonneg hp hp2 b
  have hi := positivepart_increment (a := (1/2:ℝ)) (t := |b|)
    (h := c^2*ceilingPolynomial p b+c^(5/2:ℝ)) (by positivity)
  have he : (c^2*ceilingPolynomial p b+c^(5/2:ℝ))/c^2 = ceilingPolynomial p b+c^(1/2:ℝ) := by
    rw [add_div,mul_div_cancel_left₀ _ (pow_ne_zero _ hc.ne'),rpow_five_halves_div_square hc]
  unfold capIncrementQuotient
  rw [← add_assoc] at hi
  exact ⟨div_nonneg hi.1 (sq_nonneg c),(div_le_div_of_nonneg_right hi.2 (sq_nonneg c)).trans_eq he⟩

lemma capIncrementQuotient_inside {p c b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 < c) (hb : |b| ≤ 1/2) :
    capIncrementQuotient p c b = ceilingPolynomial p b+c^(1/2:ℝ) := by
  have hd := ceiling_nonneg hp hp2 b
  have hn : 0 ≤ c^2*ceilingPolynomial p b+c^(5/2:ℝ) := by positivity
  unfold capIncrementQuotient
  rw [max_eq_left (by linarith),max_eq_left (by linarith)]
  have he : ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-|b|-(1/2-|b|)) =
      c^2*ceilingPolynomial p b+c^(5/2:ℝ) := by ring
  rw [he,add_div,mul_div_cancel_left₀ _ (pow_ne_zero _ hc.ne'),rpow_five_halves_div_square hc]

lemma ceilingPolynomial_continuous (p : ℝ) : Continuous (ceilingPolynomial p) := by
  unfold ceilingPolynomial
  fun_prop

lemma singular_ceiling_eventually (p : ℝ) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ b : ℝ, |b| ≤ 2 →
      (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (ceilingPolynomial_continuous p).continuousOn
  have ht : Tendsto (fun c : ℝ => c^2*C+c^(5/2:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ((h0.pow 2).mul_const C).add (right_rpow_tendsto_zero (q := (5/2:ℝ)) (by norm_num))
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<3/2))] with c hc b hb
  have h := (le_abs_self (ceilingPolynomial p b)).trans (by simpa only [Real.norm_eq_abs] using hC b (abs_le.mp hb))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg c)
  linarith

lemma capIncrementQuotient_tendsto {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (b : ℝ) :
    Tendsto (fun c : ℝ => capIncrementQuotient p c b) (𝓝[>] 0)
      (𝓝 ((Icc (-(1/2:ℝ)) (1/2)).indicator (ceilingPolynomial p) b)) := by
  by_cases hb : |b| ≤ 1/2
  · rw [Set.indicator_of_mem (show b ∈ Icc (-(1/2:ℝ)) (1/2) from abs_le.mp hb)]
    have h : Tendsto (fun c : ℝ => ceilingPolynomial p b+c^(1/2:ℝ)) (𝓝[>] 0)
        (𝓝 (ceilingPolynomial p b)) := by
      simpa using (right_rpow_tendsto_zero (q := (1/2:ℝ)) (by norm_num)).const_add (ceilingPolynomial p b)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (capIncrementQuotient_inside hp hp2 hc hb).symm
  · rw [Set.indicator_of_notMem (by simpa only [mem_Icc,← abs_le] using hb)]
    have ht : Tendsto (fun c : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ))
        (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.add ((h0.pow 2).mul_const (ceilingPolynomial p b))).add
        (right_rpow_tendsto_zero (q := (5/2:ℝ)) (by norm_num))
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (gt_mem_nhds (lt_of_not_ge hb))] with c hc
    unfold capIncrementQuotient
    rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    simp

lemma capIncrementQuotient_integral_tendsto {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    Tendsto (fun c : ℝ => ∫ b in Icc (-2:ℝ) 2, capIncrementQuotient p c b) (𝓝[>] 0)
      (𝓝 (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b)) := by
  have hm : ∀ c : ℝ, Continuous (capIncrementQuotient p c) := by
    intro c
    unfold capIncrementQuotient
    exact (((continuous_const.add (continuous_const.mul (ceilingPolynomial_continuous p))).add continuous_const).sub continuous_abs).max continuous_const |>.sub
      ((continuous_const.sub continuous_abs).max continuous_const) |>.div_const _
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-2:ℝ) 2)) (fun b => ceilingPolynomial p b+1)
    (Filter.Eventually.of_forall (fun c => (hm c).aestronglyMeasurable))
    (show ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ᵐ b ∂volume.restrict (Icc (-2:ℝ) 2),
      ‖capIncrementQuotient p c b‖ ≤ ceilingPolynomial p b+1 from by
      have he : ∀ᶠ c : ℝ in 𝓝[>] 0, c ≤ 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds |>.mono (fun _ h => h.le)
      filter_upwards [self_mem_nhdsWithin,he] with c hc hc1
      exact Filter.Eventually.of_forall (fun b => by
        obtain ⟨h0,h1⟩ := capIncrementQuotient_nonneg_bound hp hp2 hc (b := b)
        rw [Real.norm_eq_abs,abs_of_nonneg h0]
        exact h1.trans (by linarith [Real.rpow_le_one (z := (1/2:ℝ)) hc.le hc1 (by norm_num)])))
    (((ceilingPolynomial_continuous p).add continuous_const).continuousOn.integrableOn_Icc)
    (Filter.Eventually.of_forall (capIncrementQuotient_tendsto hp hp2))
  have he : (∫ b in Icc (-2:ℝ) 2, (Icc (-(1/2:ℝ)) (1/2)).indicator (ceilingPolynomial p) b) =
      ∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b := by
    rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
    congr 2
    apply Set.inter_eq_left.mpr
    intro b hb
    constructor <;> linarith [hb.1,hb.2]
  exact he ▸ h

lemma singularDomain_volume_difference {p gamma c : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 < c) (hd : c^gamma ≤ (1/2:ℝ))
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2) :
    (volume.real (singularDomain p gamma c)-(1/4-(c^gamma)^2))/c^2 =
      ∫ b in Icc (-2:ℝ) 2, capIncrementQuotient p c b := by
  have hv := coneBand_volume (d := c^gamma) (a := (1/2:ℝ)) (by positivity) hd
  norm_num at hv
  rw [← hv,singularDomain_volume_vertical p gamma c hcap,coneBand_volume_vertical (by norm_num)]
  have hI₁ : IntegrableOn (fun b : ℝ => max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-max (c^gamma) |b|) 0)
      (Icc (-2:ℝ) 2) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    exact (((continuous_const.add (continuous_const.mul (ceilingPolynomial_continuous p))).add continuous_const).sub
      (continuous_const.max continuous_abs)).max continuous_const
  have hI₂ : IntegrableOn (fun b : ℝ => max ((1/2:ℝ)-max (c^gamma) |b|) 0) (Icc (-2:ℝ) 2) := by
    apply ContinuousOn.integrableOn_Icc
    exact ((continuous_const.sub (continuous_const.max continuous_abs)).max continuous_const).continuousOn
  rw [← integral_sub hI₁ hI₂,← integral_div]
  apply setIntegral_congr_fun measurableSet_Icc
  intro b _
  unfold capIncrementQuotient
  apply congrArg (fun x : ℝ => x/c^2)
  have he := positivepart_floor_increment (a := (1/2:ℝ)) (d := c^gamma)
    (h := c^2*ceilingPolynomial p b+c^(5/2:ℝ)) (t := |b|) hd
    (by have := ceiling_nonneg hp hp2 b; positivity)
  simpa only [← add_assoc] using he

lemma singularDomain_volume_tendsto {p gamma : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Tendsto (fun c : ℝ => (volume.real (singularDomain p gamma c)-1/4)/c^2) (𝓝[>] 0)
      (𝓝 (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b)) := by
  have h := (capIncrementQuotient_integral_tendsto hp hp2).sub (singular_tip_small hg).tendsto_div_nhds_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,singular_ceiling_eventually p,
    (right_rpow_tendsto_zero (lt_trans (by norm_num) hg)).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with c hc hcap hd
  rw [← singularDomain_volume_difference hp hp2 hc hd.le hcap]
  ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularEnergy_nonneg (p : ℝ) (z : Plane) : 0 ≤ singularEnergy p z := by
  unfold singularEnergy
  positivity

lemma singularEnergy_measurable (p : ℝ) : Measurable (singularEnergy p) := by
  unfold singularEnergy singularField
  simp only [vec2_apply_zero,vec2_apply_one]
  fun_prop

lemma singularField_zero {p : ℝ} (hp : 1 < p) : singularField p 0 = 0 := by
  ext i
  fin_cases i <;> simp [singularField,vec2,Real.zero_rpow (show p-1 ≠ 0 by linarith)]

lemma singularEnergy_zero {p : ℝ} (hp : 1 < p) : singularEnergy p 0 = 0 := by
  simp [singularEnergy,singularField_zero hp]

lemma singularEnergy_bounded {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ coneTriangle 2, singularEnergy p z ≤ C := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  let B := C*(2:ℝ)^(p-1)
  have hB : 0 ≤ B := mul_nonneg (by linarith) (by positivity)
  refine ⟨3*B^2,by positivity,?_⟩
  intro z hz
  have hv : ‖singularField p z‖ ≤ B := by
    by_cases hzr : z 1 = 0
    · have he : z = 0 := by
        have hb : z 0 = 0 := abs_nonpos_iff.mp (hz.2.2.trans_eq hzr)
        ext i
        fin_cases i <;> assumption
      rw [he,singularField_zero hp,norm_zero]
      exact hB
    · have hz1 : 0 < z 1 := lt_of_le_of_ne hz.1 (Ne.symm hzr)
      exact (hbound z hz1 (hz.2.2.trans (by linarith))).1.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.1 hz.2.1 (by linarith)) (by linarith))
  have hx := (plane_coordinate_le (singularField p z) 0).trans hv
  have hy := (plane_coordinate_le (singularField p z) 1).trans hv
  have hx' := sq_le_sq₀ (abs_nonneg _) hB |>.mpr hx
  have hy' := sq_le_sq₀ (abs_nonneg _) hB |>.mpr hy
  simp only [sq_abs] at hx' hy'
  unfold singularEnergy
  nlinarith only [hx',hy']

lemma singularEnergy_integrable {p : ℝ} (hp : 1 < p) :
    IntegrableOn (singularEnergy p) (coneTriangle 2) := by
  obtain ⟨C,_,hC⟩ := singularEnergy_bounded hp
  apply IntegrableOn.of_bound (coneTriangle_isCompact 2).measure_lt_top
    (singularEnergy_measurable p).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (coneTriangle_isCompact 2).measurableSet] with z hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg (singularEnergy_nonneg p z)] using hC z hz

lemma energyCorrection_measurable (p c : ℝ) : Measurable (energyCorrection p c) := by
  unfold energyCorrection
  have hm := singularEnergy_measurable p
  fun_prop

lemma energy_sqrt_ge_one (p c : ℝ) (z : Plane) :
    1 ≤ Real.sqrt (1+c^2*singularEnergy p z) := by
  have he := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+c^2*singularEnergy p z by
    nlinarith only [mul_nonneg (sq_nonneg c) (singularEnergy_nonneg p z)])
  simpa only [Real.sqrt_one] using he

lemma energyCorrection_norm (p c : ℝ) (z : Plane) :
    ‖energyCorrection p c z‖ ≤ singularEnergy p z/2 := by
  have hH := singularEnergy_nonneg p z
  have hs := energy_sqrt_ge_one p c z
  unfold energyCorrection
  rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_nonneg hH,
    abs_of_pos (by nlinarith : 0 < Real.sqrt (1+c^2*singularEnergy p z)*(Real.sqrt (1+c^2*singularEnergy p z)+1))]
  apply div_le_div_of_nonneg_left hH (by norm_num)
  nlinarith

lemma physicalWeight_energy (p c : ℝ) (z : Plane) :
    physicalWeight (Real.sqrt 2) (c • singularField p z) =
      1/Real.sqrt (1+c^2*singularEnergy p z) := by
  unfold physicalWeight singularEnergy
  simp only [PiLp.smul_apply,smul_eq_mul,Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  congr 2
  ring

lemma physicalWeight_energy_expansion (p c : ℝ) (z : Plane) :
    physicalWeight (Real.sqrt 2) (c • singularField p z) = 1+c^2*energyCorrection p c z := by
  have hH := singularEnergy_nonneg p z
  have hs := energy_sqrt_ge_one p c z
  have hs0 : Real.sqrt (1+c^2*singularEnergy p z) ≠ 0 := by linarith
  have hs1 : Real.sqrt (1+c^2*singularEnergy p z)+1 ≠ 0 := by linarith
  have he := Real.sq_sqrt (show 0 ≤ 1+c^2*singularEnergy p z by positivity)
  rw [physicalWeight_energy]
  unfold energyCorrection
  field_simp
  nlinarith only [he]

lemma energyCorrection_tendsto (p : ℝ) (z : Plane) :
    Tendsto (fun c : ℝ => energyCorrection p c z) (𝓝[>] 0) (𝓝 (-singularEnergy p z/2)) := by
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun c : ℝ => Real.sqrt (1+c^2*singularEnergy p z)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun c : ℝ => 1+c^2*singularEnergy p z) (𝓝[>] 0) (𝓝 1) := by
      simpa using ((h0.pow 2).mul_const (singularEnergy p z)).const_add 1
    simpa only [Real.sqrt_one] using h.sqrt
  have hd : Tendsto (fun c : ℝ => Real.sqrt (1+c^2*singularEnergy p z)*(Real.sqrt (1+c^2*singularEnergy p z)+1)) (𝓝[>] 0) (𝓝 2) := by
    convert hs.mul (hs.add (tendsto_const_nhds (x := (1:ℝ)))) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  exact tendsto_const_nhds.div hd (by norm_num)

lemma singularDomain_subset_cone (p gamma c : ℝ) : singularDomain p gamma c ⊆ coneTriangle 2 := by
  intro z hz
  exact ⟨(abs_nonneg _).trans hz.2.2.1,hz.2.1,hz.2.2.1⟩

lemma singularDomain_eventually_mem {p gamma : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hg : 0 < gamma)
    {z : Plane} (hz : z ∈ coneTriangle 2) (hz1 : 0 < z 1) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, z ∈ singularDomain p gamma c ↔ z ∈ coneTriangle (1/2) := by
  by_cases hr : z 1 ≤ 1/2
  · filter_upwards [self_mem_nhdsWithin,
      (right_rpow_tendsto_zero hg).eventually (gt_mem_nhds hz1)] with c hc hd
    have hm : z ∈ singularDomain p gamma c := by
      refine ⟨hd.le,hz.2.1,hz.2.2,hr.trans ?_⟩
      have hn := ceiling_nonneg hp hp2 (z 0)
      have hn' : 0 ≤ c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ) :=
        add_nonneg (mul_nonneg (sq_nonneg c) hn) (Real.rpow_nonneg hc.le _)
      linarith
    exact ⟨fun _ => ⟨hz.1,hr,hz.2.2⟩,fun _ => hm⟩
  · have ht : Tendsto (fun c : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ))
        (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.add ((h0.pow 2).mul_const (ceilingPolynomial p (z 0)))).add
        (right_rpow_tendsto_zero (q := (5/2:ℝ)) (by norm_num))
    filter_upwards [ht.eventually (gt_mem_nhds (lt_of_not_ge hr))] with c hc
    exact ⟨fun h => False.elim (not_le_of_gt hc h.2.2.2),fun h => False.elim (hr h.2.1)⟩

lemma energyCorrection_integral_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 0 < gamma) :
    Tendsto (fun c : ℝ => ∫ z in singularDomain p gamma c, energyCorrection p c z) (𝓝[>] 0)
      (𝓝 (-(∫ z in coneTriangle (1/2), singularEnergy p z)/2)) := by
  have ht : Tendsto (fun c : ℝ => ∫ z in coneTriangle 2,
      (singularDomain p gamma c).indicator (energyCorrection p c) z) (𝓝[>] 0)
      (𝓝 (∫ z in coneTriangle 2, (coneTriangle (1/2)).indicator (fun z => -singularEnergy p z/2) z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => singularEnergy p z/2)
    · exact Filter.Eventually.of_forall (fun c =>
        ((energyCorrection_measurable p c).indicator (singularDomain_isCompact p gamma c).measurableSet).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall (fun z => by
        by_cases hz : z ∈ singularDomain p gamma c
        · rw [Set.indicator_of_mem hz]
          exact energyCorrection_norm p c z
        · rw [Set.indicator_of_notMem hz,norm_zero]
          exact div_nonneg (singularEnergy_nonneg p z) (by norm_num)))
    · exact (singularEnergy_integrable hp).div_const 2
    · filter_upwards [ae_restrict_mem (coneTriangle_isCompact 2).measurableSet] with z hz
      by_cases hzr : z 1 = 0
      · have he : z = 0 := by
          have hb : z 0 = 0 := abs_nonpos_iff.mp (hz.2.2.trans_eq hzr)
          ext i
          fin_cases i <;> assumption
        subst z
        have he : ∀ c : ℝ, energyCorrection p c 0 = 0 := by simp [energyCorrection,singularEnergy_zero hp]
        simp [Set.indicator,he,singularEnergy_zero hp]
      · have he := singularDomain_eventually_mem (le_trans (by norm_num) hp.le) hp2 hg hz
          (lt_of_le_of_ne hz.1 (Ne.symm hzr))
        by_cases hza : z ∈ coneTriangle (1/2)
        · rw [Set.indicator_of_mem hza]
          apply (energyCorrection_tendsto p z).congr'
          filter_upwards [he] with c hc
          exact (Set.indicator_of_mem (hc.mpr hza) _).symm
        · rw [Set.indicator_of_notMem hza]
          apply tendsto_const_nhds.congr'
          filter_upwards [he] with c hc
          exact (Set.indicator_of_notMem (fun h => hza (hc.mp h)) _).symm
  have he₁ : ∀ c : ℝ, (∫ z in coneTriangle 2, (singularDomain p gamma c).indicator (energyCorrection p c) z) =
      ∫ z in singularDomain p gamma c, energyCorrection p c z := by
    intro c
    rw [integral_indicator (singularDomain_isCompact p gamma c).measurableSet,
      Measure.restrict_restrict (singularDomain_isCompact p gamma c).measurableSet,
      Set.inter_eq_left.mpr (singularDomain_subset_cone p gamma c)]
  have he₂ : (∫ z in coneTriangle 2, (coneTriangle (1/2)).indicator (fun z => -singularEnergy p z/2) z) =
      -(∫ z in coneTriangle (1/2), singularEnergy p z)/2 := by
    rw [integral_indicator (coneTriangle_isCompact (1/2)).measurableSet,
      Measure.restrict_restrict (coneTriangle_isCompact (1/2)).measurableSet,
      Set.inter_eq_left.mpr (show coneTriangle (1/2) ⊆ coneTriangle 2 from fun z hz =>
        ⟨hz.1,hz.2.1.trans (by norm_num),hz.2.2⟩),integral_div,integral_neg]
  simpa only [he₁,he₂] using ht

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_EnergyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceilingPolynomial_integral (p : ℝ) :
    (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) = (p+3)/120 := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2)]
  have he : ceilingPolynomial p = fun b => (p/4)*b^2+(2-p)*b^4 := by
    funext b
    unfold ceilingPolynomial
    ring
  rw [he,intervalIntegral.integral_add ((by fun_prop : Continuous (fun b : ℝ => (p/4)*b^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun b : ℝ => (2-p)*b^4)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_pow,integral_pow]
  norm_num
  ring

lemma angularEnergy_integral (p : ℝ) :
    (∫ eta in (-1:ℝ)..1, angularEnergy p eta) = 2*(2*p^2+2*p+13)/15 := by
  have he : angularEnergy p = fun eta => p^2/4+(p*(2-p)/2+2)*eta^2+((2-p)^2/4)*eta^4 := by
    funext eta
    unfold angularEnergy
    ring
  have hI₁ : IntervalIntegrable (fun eta : ℝ => p^2/4+(p*(2-p)/2+2)*eta^2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun eta : ℝ => p^2/4+(p*(2-p)/2+2)*eta^2)).intervalIntegrable _ _
  have hI₂ : IntervalIntegrable (fun eta : ℝ => ((2-p)^2/4)*eta^4) volume (-1) 1 :=
    (by fun_prop : Continuous (fun eta : ℝ => ((2-p)^2/4)*eta^4)).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_add hI₁ hI₂,
    intervalIntegral.integral_add (intervalIntegrable_const)
      ((by fun_prop : Continuous (fun eta : ℝ => (p*(2-p)/2+2)*eta^2)).intervalIntegrable _ _),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_pow,integral_pow]
  norm_num
  ring

lemma singularEnergy_polar (p eta : ℝ) {r : ℝ} (hr : 0 < r) :
    singularEnergy p (vec2 (r*eta) r) = (1/4:ℝ)*(2*r)^(2*p-2)*angularEnergy p eta := by
  have he : (2*r) • vec2 (eta/2) (1/2) = vec2 (r*eta) r := by
    ext i
    fin_cases i
    · change (2*r)*(eta/2)=r*eta
      ring
    · change (2*r)*(1/2)=r
      ring
  have hv := singularField_smul p (show 0 < 2*r by positivity)
    (z := vec2 (eta/2) (1/2)) (by norm_num)
  rw [he,singularField_level] at hv
  have hpw : (2*r)^(2*p-2) = ((2*r)^(p-1))^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    congr 1
    ring
  unfold singularEnergy
  rw [hv,hpw]
  simp only [PiLp.smul_apply,smul_eq_mul,vec2_apply_zero,vec2_apply_one]
  unfold angularEnergy
  ring

lemma singularEnergy_slice_integral {p : ℝ} (hp : 1 < p) {r : ℝ} (hr : 0 ≤ r) :
    (∫ b in Icc (-r) r, singularEnergy p (vec2 b r)) =
      (2*r)^(2*p-1)/8 * (∫ eta in (-1:ℝ)..1, angularEnergy p eta) := by
  by_cases hr0 : r = 0
  · subst r
    simp [Real.zero_rpow (show 2*p-1 ≠ 0 by linarith)]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1:ℝ)) (b := 1) (fun b : ℝ => singularEnergy p (vec2 b r)) r
  simp only [smul_eq_mul,mul_neg_one,mul_one] at hs
  rw [← hs]
  have hi : (∫ eta in (-1:ℝ)..1, singularEnergy p (vec2 (r*eta) r)) =
      (1/4:ℝ)*(2*r)^(2*p-2)*(∫ eta in (-1:ℝ)..1, angularEnergy p eta) := by
    simp_rw [singularEnergy_polar p _ hrp]
    exact intervalIntegral.integral_const_mul _ _
  rw [hi,show 2*p-1=2*p-2+1 by ring,Real.rpow_add_one (by positivity : 2*r ≠ 0)]
  ring

lemma singular_radial_integral {p : ℝ} (hp : 0 < p) :
    (∫ r in (0:ℝ)..(1/2:ℝ), (2*r)^(2*p-1)) = 1/(4*p) := by
  have he := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (1/2:ℝ))
    (fun r : ℝ => r^(2*p-1)) (c := (2:ℝ)) (by norm_num)
  norm_num only [mul_zero,mul_one_div_cancel (by norm_num : (2:ℝ) ≠ 0),smul_eq_mul] at he
  rw [he,integral_rpow (Or.inl (by linarith : -1 < 2*p-1))]
  rw [show 2*p-1+1=2*p by ring,Real.one_rpow,Real.zero_rpow (by positivity : 2*p ≠ 0)]
  field_simp
  ring

lemma singularEnergy_integral {p : ℝ} (hp : 1 < p) :
    (∫ z in coneTriangle (1/2), singularEnergy p z) = (2*p^2+2*p+13)/(240*p) := by
  have hsub : coneTriangle (1/2) ⊆ coneTriangle 2 := fun z hz =>
    ⟨hz.1,hz.2.1.trans (by norm_num),hz.2.2⟩
  have heq : ∀ z : Plane, z ∈ coneTriangle (1/2) ↔
      z 1 ∈ Icc (0:ℝ) (1/2) ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneTriangle,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_setIntegral_horizontal_interval (coneTriangle_isCompact (1/2)).measurableSet
    ((singularEnergy_integrable hp).mono_set hsub) (s := Icc (0:ℝ) (1/2))
    (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc (0:ℝ) (1/2), ∫ b in Icc (-r) r, singularEnergy p (vec2 b r)) =
      ∫ r in Icc (0:ℝ) (1/2), (2*r)^(2*p-1)/8*(∫ eta in (-1:ℝ)..1, angularEnergy p eta) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    exact singularEnergy_slice_integral hp hr.1
  simp only [id_eq]
  rw [he,angularEnergy_integral p]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  have hf : (fun r : ℝ => (2*r)^(2*p-1)/8*(2*(2*p^2+2*p+13)/15)) =
      fun r => (2*(2*p^2+2*p+13)/15/8)*(2*r)^(2*p-1) := by funext r; ring
  rw [hf,intervalIntegral.integral_const_mul,singular_radial_integral (by linarith : 0 < p)]
  field_simp
  ring

lemma singular_exact_coefficient {p : ℝ} (hp : 1 < p) :
    (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) -
      (∫ z in coneTriangle (1/2), singularEnergy p z)/2 = singularCoefficient p := by
  rw [ceilingPolynomial_integral,singularEnergy_integral hp]
  unfold singularCoefficient
  have hp0 : p ≠ 0 := by linarith
  field_simp
  ring

lemma energyCorrection_integrable {p : ℝ} (hp : 1 < p) (gamma c : ℝ) :
    IntegrableOn (energyCorrection p c) (singularDomain p gamma c) := by
  apply ((singularEnergy_integrable hp).mono_set (singularDomain_subset_cone p gamma c)).div_const 2 |>.mono'
    (energyCorrection_measurable p c).aestronglyMeasurable
  exact Filter.Eventually.of_forall (energyCorrection_norm p c)

lemma singular_weighted_integral_expansion {p : ℝ} (hp : 1 < p) (gamma c : ℝ) :
    (∫ z in singularDomain p gamma c, physicalWeight (Real.sqrt 2) (c • singularField p z)) =
      volume.real (singularDomain p gamma c)+c^2*(∫ z in singularDomain p gamma c, energyCorrection p c z) := by
  simp_rw [physicalWeight_energy_expansion]
  rw [integral_add (integrableOn_const (C := (1:ℝ)) (singularDomain_isCompact p gamma c).measure_lt_top.ne)
    ((energyCorrection_integrable hp gamma c).const_mul (c^2)),integral_const_mul]
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_weighted_integral_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Tendsto (fun c : ℝ =>
      ((∫ z in singularDomain p gamma c, physicalWeight (Real.sqrt 2) (c • singularField p z))-1/4)/c^2)
      (𝓝[>] 0) (𝓝 (singularCoefficient p)) := by
  have ht := (singularDomain_volume_tendsto (by linarith : 0 ≤ p) hp2 hg).add
    (energyCorrection_integral_tendsto hp hp2 (by linarith : 0 < gamma))
  have hlim : (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) +
      -(∫ z in coneTriangle (1/2), singularEnergy p z)/2 = singularCoefficient p := by
    rw [neg_div,← sub_eq_add_neg]
    exact singular_exact_coefficient hp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [singular_weighted_integral_expansion hp gamma c]
  field_simp
  ring

lemma singular_totalCost_quotient_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Tendsto (fun c : ℝ =>
      (2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2-Real.sqrt 2/2)/c^2)
      (𝓝[>] 0) (𝓝 (2*Real.sqrt 2*singularCoefficient p)) := by
  have ht := ((singular_weighted_integral_tendsto hp hp2 hg).const_mul (2*Real.sqrt 2)).add
    ((singular_tip_small hg).tendsto_div_nhds_zero.const_mul (8*Real.sqrt 2))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards with c
  unfold singularCost
  ring

lemma singular_asymptotic {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun c => 2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2-
        (Real.sqrt 2/2+2*Real.sqrt 2*singularCoefficient p*c^2))
      (fun c => c^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have ht := (singular_totalCost_quotient_tendsto hp hp2 hg).sub_const (2*Real.sqrt 2*singularCoefficient p)
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((pow_ne_zero 2 (ne_of_gt hc)) h)

lemma singular_totalCost_small {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma)
    (hk : singularCoefficient p < 0) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2 < Real.sqrt 2/2 := by
  have hk' : 2*Real.sqrt 2*singularCoefficient p < 0 := mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) hk
  filter_upwards [self_mem_nhdsWithin,
    (singular_totalCost_quotient_tendsto hp hp2 hg).eventually (gt_mem_nhds hk')] with c hc hcost
  exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ (sq_pos_of_pos hc)).mp hcost)

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_geometric_cover {p gamma : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hpg : 0 < 1+gamma*(p-2)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      tetrahedron ⊆ singularLower p gamma c ∪ singularUpper p gamma c ∪
        lowerTip (c^gamma) ∪ upperTip (c^gamma) := by
  obtain ⟨C,_,hinv⟩ := singular_inverse_small hp2
  obtain ⟨K,_,hover⟩ := singular_overlap_small (by linarith : 0 ≤ p) hp2.le
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hcut : Tendsto (fun c : ℝ => c*C*(c^gamma)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_assoc,mul_left_comm,mul_zero] using (singular_cutoff_small hpg).const_mul C
  have hKlim : Tendsto (fun c : ℝ => c*K) (𝓝[>] 0) (𝓝 0) := by simpa using h0.mul_const K
  filter_upwards [self_mem_nhdsWithin,h0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hKlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),overlap_error_eventually K]
    with c hc hc1 hcut hcK herr
  have hc : 0 < c := hc
  intro z hz
  obtain ⟨t,ht0,ht1,hx,hy,hz2⟩ := hz
  by_cases htip : t ≤ 2*c^gamma
  · exact Or.inl (Or.inr ⟨t,ht0,htip,hy,hz2⟩)
  by_cases htip' : 1-t ≤ 2*c^gamma
  · exact Or.inr ⟨1-t,by linarith,htip',hx,by rw [hz2]; congr 1; ring⟩
  have hx1 : |z 0| ≤ 1 := hx.trans (by linarith)
  have hy1 : |z 1| ≤ 1 := hy.trans ht1
  have hkx : |c*z 0| ≤ c := by simpa only [abs_mul,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hx1 hc.le
  have hky : |-c*z 1| ≤ c := by simpa only [abs_mul,abs_neg,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hy1 hc.le
  obtain ⟨zm,hm0,hm2,hmb,hem⟩ := hinv (c^gamma) c (z 1) t (c*z 0)
    (Real.rpow_pos_of_pos hc gamma) hc.le hcut.le (by linarith) ht1 hy hkx
  obtain ⟨zp,hp0,hp2',hpb,hep⟩ := hinv (c^gamma) c (z 0) (1-t) (-c*z 1)
    (Real.rpow_pos_of_pos hc gamma) hc.le hcut.le (by linarith) (by linarith) hx hky
  have hem0 := congrArg (fun w : Plane => w 0) hem
  have hem1 := congrArg (fun w : Plane => w 1) hem
  have hep0 := congrArg (fun w : Plane => w 0) hep
  have hep1 := congrArg (fun w : Plane => w 1) hep
  change z 1 = zm 0+(c*z 0)*singularField p zm 0 at hem0
  change t = zm 1+(c*z 0)*singularField p zm 1 at hem1
  change z 0 = zp 0+(-c*z 1)*singularField p zp 0 at hep0
  change 1-t = zp 1+(-c*z 1)*singularField p zp 1 at hep1
  have hceil := hover c (z 0) (z 1) zm zp hc.le hc1.le hcK.le herr hx1 hy1 hm2 hp2' hmb hpb
    (by linarith only [hem0]) (by linarith only [hep0]) (by nlinarith only [hem1,hep1])
  rcases hceil with hm | hp'
  · apply Or.inl ∘ Or.inl ∘ Or.inl
    refine ⟨zm,⟨hm0,hm2,hmb,hm⟩,z 0,hx1,?_⟩
    ext i
    fin_cases i
    · rfl
    · change z 1 = zm 0+z 0*(c*singularField p zm 0)
      nlinarith only [hem0]
    · change z 2 = Real.sqrt 2*(zm 1+z 0*(c*singularField p zm 1))
      rw [hz2]
      congr 1
      nlinarith only [hem1]
  · apply Or.inl ∘ Or.inl ∘ Or.inr
    refine ⟨zp,⟨hp0,hp2',hpb,hp'⟩,z 1,hy1,?_⟩
    ext i
    fin_cases i
    · change z 0 = zp 0-c*z 1*singularField p zp 0
      nlinarith only [hep0]
    · rfl
    · change z 2 = Real.sqrt 2*(1-(zp 1-c*z 1*singularField p zp 1))
      rw [hz2]
      congr 1
      nlinarith only [hep1]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Singular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_hyperbolic_eventually {p gamma : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hpg : 0 < 1+gamma*(p-2)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ z ∈ singularDomain p gamma c,
      HyperbolicAt 1 (fun w => c • singularField p w) z ∧
      HyperbolicAt 1 (fun w => -c • singularField p w) z := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  have hlim : Tendsto (fun c : ℝ => C*(c*(c^gamma)^(p-2))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (singular_cutoff_small hpg).const_mul C
  filter_upwards [self_mem_nhdsWithin,hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with c hc hsmall
  have hc : 0 < c := hc
  intro z hz
  have hd : 0 < c^gamma := Real.rpow_pos_of_pos hc gamma
  have hz1 : 0 < z 1 := hd.trans_le hz.1
  have hb : |z 0| ≤ 2*z 1 := by linarith [hz.2.2.1]
  have hn := (hbound z hz1 hb).2
  have hr := Real.rpow_le_rpow_of_nonpos hd hz.1 (by linarith : p-2 ≤ 0)
  have hclt : c*‖fderiv ℝ (singularField p) z‖ < 1 := calc
    _ ≤ c*(C*(z 1)^(p-2)) := mul_le_mul_of_nonneg_left hn hc.le
    _ ≤ c*(C*(c^gamma)^(p-2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hr (by linarith)) hc.le
    _ = C*(c*(c^gamma)^(p-2)) := by ring
    _ < 1 := hsmall
  exact ⟨singularField_scaled_hyperbolic hp hp2 hc.ne' hz1 hz.2.2.1
      (by simpa only [abs_of_pos hc] using hclt),
    singularField_scaled_hyperbolic hp hp2 (neg_ne_zero.mpr hc.ne') hz1 hz.2.2.1
      (by simpa only [abs_neg,abs_of_pos hc] using hclt)⟩

lemma singular_scaled_smoothNear (p gamma k : ℝ) {c : ℝ} (hc : 0 < c) :
    SmoothNear 1 (singularDomain p gamma c) (fun z => k • singularField p z) := by
  obtain ⟨U,hU,hDU,hF⟩ := singularDomain_smoothNear p gamma hc
  exact ⟨U,hU,hDU,(hF.of_le (by norm_num : (1:WithTop ℕ∞) ≤ ∞)).const_smul k⟩

lemma physicalWeight_neg (h : ℝ) (g : Plane) : physicalWeight h (-g) = physicalWeight h g := by
  simp [physicalWeight]

lemma singularUpper_image (p gamma c : ℝ) :
    (fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
        (fun z => -c • singularField p z) 1) = singularUpper p gamma c := by
  ext z
  constructor
  · rintro ⟨_,⟨_,⟨b,hb,s,hs,rfl⟩,rfl⟩,rfl⟩
    refine ⟨b,hb,s,hs,?_⟩
    ext i
    fin_cases i <;> simp [swapReflect,vec3] <;> ring
  · rintro ⟨b,hb,s,hs,rfl⟩
    refine ⟨swapReflect (vec3 s (b 0+s*(-c • singularField p b) 0)
      (Real.sqrt 2*(b 1+s*(-c • singularField p b) 1))),
      ⟨_,⟨b,hb,s,hs,rfl⟩,rfl⟩,?_⟩
    ext i
    fin_cases i <;> simp [swapReflect,vec3] <;> ring

/-- Singular-field approximation. The positive parameter is fixed before
choosing either finite approximation, and both errors use its strict saving. -/
theorem singular : SingularStatement := by
  intro p gamma hp hp' hg hg'
  obtain ⟨hp2,hpg,_,hk⟩ := singular_parameter_bounds hp hp' hg hg'
  refine ⟨hk,singular_asymptotic hp hp2.le hg,?_⟩
  filter_upwards [self_mem_nhdsWithin,singular_geometric_cover hp hp2 hpg,
    singular_hyperbolic_eventually hp hp2 hpg,singular_totalCost_small hp hp2.le hg hk]
    with c hc hgeom hhyp hcost
  have hc : 0 < c := hc
  let eps : ℝ := (Real.sqrt 2/2-(2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2))/4
  have heps : 0 < eps := div_pos (sub_pos.mpr hcost) (by norm_num)
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hD := singularDomain_isCompact p gamma c
  obtain ⟨n,C,hC,hcovC,hcostC⟩ := physical_hyperbolic_cover hroot (by norm_num : (0:ℝ)<1)
    hD (singular_scaled_smoothNear p gamma c hc) (fun z hz => (hhyp z hz).1) heps
  have hneg := physical_hyperbolic_cover hroot (by norm_num : (0:ℝ)<1)
    hD (singular_scaled_smoothNear p gamma (-c) hc) (fun z hz => (hhyp z hz).2) heps
  simp only [neg_smul,physicalWeight_neg] at hneg
  have hupper := (hneg.isometry swapReflect.toIsometryEquiv).isometry
    (IsometryEquiv.addLeft (vec3 0 0 (Real.sqrt 2)))
  simp only [← neg_smul] at hupper
  change HasFiniteCover Cylinder.parallelogram
    ((fun z => vec3 0 0 (Real.sqrt 2)+z) ''
      (swapReflect '' physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
        (fun z => -c • singularField p z) 1)) (singularCost p gamma c+eps) at hupper
  rw [singularUpper_image] at hupper
  obtain ⟨m,D,hD,hcovD,hcostD⟩ := hupper
  refine ⟨n,m,C,D,lowerTipCylinder (c^gamma),upperTipCylinder (c^gamma),hC,hD,
    lowerTipCylinder_triangle (Real.rpow_pos_of_pos hc gamma),
    upperTipCylinder_triangle (Real.rpow_pos_of_pos hc gamma),hcovC,hcovD,
    lowerTipCylinder_carrier _,upperTipCylinder_carrier _,?_,?_⟩
  · rw [lowerTipCylinder_carrier,upperTipCylinder_carrier]
    exact hgeom.trans (union_subset_union (union_subset_union (union_subset_union hcovC hcovD) Subset.rfl) Subset.rfl)
  · rw [lowerTipCylinder_area (Real.rpow_nonneg hc.le gamma),
      upperTipCylinder_area (Real.rpow_nonneg hc.le gamma)]
    change familyArea C ≤ singularCost p gamma c+eps at hcostC
    dsimp only [eps] at hcostC hcostD
    linarith

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

theorem fullMain : FullMain :=
  ⟨hyperbolic, physicalHyperbolic, logarithmic, productCell,
    orthogonalGrid, nilpotent, singular⟩

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CylinderCovering

theorem ruledHistorical_oai : RuledApproximation.FullMain :=
  RuledApproximation.fullMain

end CylinderCovering

end OAI
end

theorem solution : type_of% @OAI.CylinderCovering.ruledHistorical_oai := @OAI.CylinderCovering.ruledHistorical_oai
