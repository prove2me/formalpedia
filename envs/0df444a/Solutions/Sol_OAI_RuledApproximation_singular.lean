-- Prove2me | solution 1 for OAI.RuledApproximation.singular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:00:02.586194+00:00
-- url     : https://prove2.me/submissions/c73c5053-85f4-4112-aa73-e5cb0f671a5b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Singular.lean:L67-L105
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular. The node keeps its source
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
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
import Definitions.Def_OAI_Geometry_RuledCovering_EnergyIntegral
import Definitions.Def_OAI_Geometry_RuledCovering_TipCylinders
import Theorems.Thm_OAI_RuledApproximation_Cylinder_translate_carrier
import Theorems.Thm_OAI_RuledApproximation_HasFiniteCover_isometry
import Theorems.Thm_OAI_RuledApproximation_IsTriangle_linear_image
import Theorems.Thm_OAI_RuledApproximation_coneBand_volume
import Theorems.Thm_OAI_RuledApproximation_coneBand_volume_vertical
import Theorems.Thm_OAI_RuledApproximation_coneTriangle_isCompact
import Theorems.Thm_OAI_RuledApproximation_coneTriangle_volume
import Theorems.Thm_OAI_RuledApproximation_energyCorrection_integral_tendsto
import Theorems.Thm_OAI_RuledApproximation_globalize_local_covers
import Theorems.Thm_OAI_RuledApproximation_hyperbolic_local_patch
import Theorems.Thm_OAI_RuledApproximation_plane_setIntegral_horizontal_interval
import Theorems.Thm_OAI_RuledApproximation_projectedCylinder_mem_iff
import Theorems.Thm_OAI_RuledApproximation_singularDomain_isCompact
import Theorems.Thm_OAI_RuledApproximation_singularDomain_volume_vertical
import Theorems.Thm_OAI_RuledApproximation_singularField_contDiffAt
import Theorems.Thm_OAI_RuledApproximation_singularField_homogeneous_bounds
import Theorems.Thm_OAI_RuledApproximation_singularField_scaled_hyperbolic
import Theorems.Thm_OAI_RuledApproximation_singularField_smul
import Theorems.Thm_OAI_RuledApproximation_singular_geometric_cover
import Theorems.Thm_OAI_RuledApproximation_singular_tip_small

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

lemma perpendicularProjection_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (perpendicularProjection h g) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hn
  have hz := LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hn
  rw [perpendicularProjection_normDet hh, physicalWeight_eq_inv_norm] at hz
  have hp : 0 < h * (1 / ‖physicalDirection h g‖) :=
    mul_pos hh (one_div_pos.mpr (physicalDirection_norm_pos h g))
  exact hp.ne' hz

lemma projectedCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).area = h * volume.real P * physicalWeight h g := by
  rw [Cylinder.area, projectedCylinder, perpendicularProjection_volume hh]
  ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

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

-- ---- from OAI.Geometry.RuledCovering.Isometries ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

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

lemma Cylinder.translate_area (C : Cylinder) (q : Space) :
    (C.translate q).area = C.area := by
  change volume.real ((fun b => C.transversePart q + b) '' C.base) = volume.real C.base
  have he := (measurePreserving_add_left volume (C.transversePart q)).setIntegral_image_emb
    (Homeomorph.addLeft (C.transversePart q)).measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularField ----
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

lemma singularField_contDiffOn (p : ℝ) :
    ContDiffOn ℝ ∞ (singularField p) {z : Plane | 0 < z 1} :=
  fun _ hz => (singularField_contDiffAt p hz).contDiffWithinAt

lemma singularField_level (p b : ℝ) :
    singularField p (vec2 b (1/2)) = vec2 (p/4+(2-p)*b^2) b := by
  ext i
  fin_cases i <;> simp [singularField,vec2]; ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

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

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularOverlap ----
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

lemma right_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 ((0:ℝ)^q)) :=
    ((Real.continuous_rpow_const hq.le).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq.ne'] using h

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.CapAsymptotics ----
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

-- ---- from OAI.Geometry.RuledCovering.SingularEnergy ----
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

lemma singularDomain_subset_cone (p gamma c : ℝ) : singularDomain p gamma c ⊆ coneTriangle 2 := by
  intro z hz
  exact ⟨(abs_nonneg _).trans hz.2.2.1,hz.2.1,hz.2.2.1⟩

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.EnergyIntegral ----
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

-- ---- from OAI.Geometry.RuledCovering.SingularAsymptotics ----
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

-- ---- from OAI.Geometry.RuledCovering.TipCylinders ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

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

-- ---- from OAI.Geometry.RuledCovering.Singular ----
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

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular := @_root_.OAI.RuledApproximation.singular
