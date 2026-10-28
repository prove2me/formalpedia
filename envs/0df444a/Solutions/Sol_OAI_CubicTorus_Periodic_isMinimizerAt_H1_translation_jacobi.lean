-- Prove2me | solution 1 for OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:53:31.939345+00:00
-- url     : https://prove2.me/submissions/2a14946f-2533-4fa6-b505-14578df614c1

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_global_normal_stability
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_curvature_nonnegative
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_normalComponentScalar_global_jacobi

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma admissible_neg {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (fun x => -F x) := by
  refine ⟨hF.1.neg, ?_, ?_⟩
  · intro n x
    change -F (x + latticeVector n) = -F x
    rw [hF.2.1 n x]
  · intro x
    simpa using hF.2.2 x

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

lemma abs_flux_le_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ (perimeter E).toReal := by
  apply abs_le.mpr
  constructor
  · have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y => -F y) x) ≤ perimeter E :=
      le_iSup_of_le (fun y => -F y) (le_iSup_of_le (admissible_neg hF) le_rfl)
    simp_rw [divergence_neg, integral_neg] at hh
    have := (ENNReal.ofReal_le_iff_le_toReal hE).mp hh
    linarith
  · exact (ENNReal.ofReal_le_iff_le_toReal hE).mp
      (le_iSup_of_le F (le_iSup_of_le hF le_rfl))

lemma abs_flux_le_mul_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ k * (perimeter E).toReal := by
  have hG : AdmissibleField (fun x => k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      calc
        k⁻¹ * ‖F x‖ ≤ k⁻¹ * k := mul_le_mul_of_nonneg_left (hb x) (by positivity)
        _ = 1 := inv_mul_cancel₀ hk.ne'
  have hg := abs_flux_le_perimeter hE hG
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hk)] at hg
  calc
    _ = k * (k⁻¹ * |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hk.le

end CubicTorus

namespace CubicTorus

lemma abs_directional_flux_le {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f x a|
      ≤ ‖a‖ * (perimeter E).toReal := by
  by_cases ha : a = 0
  · simp [ha]
  have hd := hf.differentiable (by simp)
  have hfield : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • a) := hf.smul_const a
  have hfieldp : ∀ n x, f (x + latticeVector n) • a = f x • a := by
    intro n x
    rw [hp]
  have hfieldb : ∀ x, ‖f x • a‖ ≤ ‖a‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg a) (hb x)
  simpa only [divergence_smul_const hd.differentiableAt] using
    abs_flux_le_mul_perimeter hE hfield hfieldp (norm_pos_iff.mpr ha) hfieldb

end CubicTorus

namespace CubicTorus

theorem smooth_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) : |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      fderiv ℝ f (x + t • a) a| ≤ ‖a‖ * (perimeter E).toReal := by
    have hp' : ∀ n x, f ((x + latticeVector n) + t • a) = f (x + t • a) := by
      intro n x
      rw [add_right_comm, hp]
    simpa only [Function.comp_def, id_eq, fderiv_comp_add_right] using
      abs_directional_flux_le hE (hf.comp (contDiff_id.add contDiff_const)) hp'
        (fun x => hb (x + t • a)) a
  calc
    _ = ‖∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a‖ := by
      simp_rw [hFTC, Real.norm_eq_abs]
    _ = ‖∫ t in Ioc (0 : ℝ) 1,
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a‖ := by
      rw [integral_integral_swap hi]
    _ ≤ (‖a‖ * (perimeter E).toReal) * (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      exact Filter.Eventually.of_forall fun t => (Real.norm_eq_abs _).trans_le (ht t)
    _ = _ := by simp [Measure.real]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma mollifier_rOut_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  simpa only [mollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma smoothApprox_periodic {g : Cover → ℝ}
    (hp : ∀ n x, g (x + latticeVector n) = g x) (k : ℕ) (n : Fin 3 → ℤ) (x : Cover) :
    smoothApprox g k (x + latticeVector n) = smoothApprox g k x := by
  simp only [smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show x + latticeVector n - y = (x - y) + latticeVector n by abel, hp]

lemma smoothApprox_ae_tendsto {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothApprox g n x) atTop (𝓝 (g x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    mollifier_rOut_tendsto (K := 2) _ (locallyIntegrable_of_bounded hg hb)
  exact Eventually.of_forall fun n => by dsimp [mollifier]; ring_nf; rfl

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem measurable_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply le_of_tendsto hi.abs
  exact Eventually.of_forall fun n => smooth_test_translation_bound hE
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n) a

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicTorus

lemma setIntegral_lift_measurable {f : Torus → ℝ} (hf : Measurable f)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f z ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f (quotientMap x) := by
  change (∫ z in E, f z ∂Measure.map quotientMap (volume.restrict fundamentalCube)) = _
  rw [setIntegral_map hE hf.aestronglyMeasurable measurable_quotientMap.aemeasurable,
    Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma torus_test_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {g : Torus → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume|
      ≤ ‖a‖ * (perimeter E).toReal := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_translation_bound hP (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) a

lemma integral_difference_test {E : Set Torus} (hE : MeasurableSet E)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) (a : Torus) :
    (∫ x in E, (g (x + a) - g x) ∂torusVolume) =
      ∫ x, (characteristic E (x - a) - characteristic E x) * g x ∂torusVolume := by
  have hi₁ : Integrable (fun x => characteristic E x * g (x + a)) torusVolume := by
    apply Integrable.of_bound ((measurable_characteristic hE).mul
      (hg.comp (measurable_id.add_const a))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E x)).trans (hb (x + a))
  have hi₂ : Integrable (fun x => characteristic E x * g x) torusVolume := by
    apply Integrable.of_bound ((measurable_characteristic hE).mul hg).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E x)).trans (hb x)
  have hi₃ : Integrable (fun x => characteristic E (x - a) * g x) torusVolume := by
    apply Integrable.of_bound (((measurable_characteristic hE).comp
      (measurable_id.sub_const a)).mul hg).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E (x - a))).trans (hb x)
  have hs := (measurePreserving_add_right torusVolume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding (fun x => characteristic E (x - a) * g x)
  simp only [add_sub_cancel_right] at hs
  calc
    _ = ∫ x, characteristic E x * (g (x + a) - g x) ∂torusVolume := by
      rw [← integral_indicator hE]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        classical
        by_cases hx : x ∈ E <;> simp [characteristic, hx]
    _ = (∫ x, characteristic E x * g (x + a) ∂torusVolume) -
        ∫ x, characteristic E x * g x ∂torusVolume := by
      simp_rw [mul_sub]
      exact integral_sub hi₁ hi₂
    _ = (∫ x, characteristic E (x - a) * g x ∂torusVolume) -
        ∫ x, characteristic E x * g x ∂torusVolume := by rw [hs]
    _ = _ := by simp_rw [sub_mul]; exact (integral_sub hi₃ hi₂).symm

theorem characteristic_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (a : Cover) :
    (∫ x, |characteristic E (x - quotientMap a) - characteristic E x| ∂torusVolume)
      ≤ ‖a‖ * (perimeter E).toReal := by
  let g : Torus → ℝ := fun x => characteristic E (x - quotientMap a) - characteristic E x
  have hg : Measurable g := ((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)
  have hb (x) : |g x| ≤ 1 := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
  have heq (x) : g x * g x = |g x| := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
  have h := torus_test_translation_bound hE hP hg hb a
  rw [integral_difference_test hE hg hb] at h
  change |∫ x, g x * g x ∂torusVolume| ≤ _ at h
  simp_rw [heq] at h
  rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg (g x))] at h
  exact h

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma characteristic_translation_ae_of_perimeter_zero {E : Set Torus}
    (hE : MeasurableSet E) (hP : perimeter E = 0) (a : Torus) :
    (fun x ↦ characteristic E (x - a)) =ᵐ[torusVolume] characteristic E := by
  have h := characteristic_translation_bound hE (hP ▸ ENNReal.zero_ne_top) (representative a)
  rw [quotientMap_representative, hP, ENNReal.toReal_zero, mul_zero] at h
  have hg : Measurable (fun x ↦ |characteristic E (x - a) - characteristic E x|) :=
    (((measurable_characteristic hE).comp (measurable_id.sub_const a)).sub
      (measurable_characteristic hE)).abs
  have hi : Integrable (fun x ↦ |characteristic E (x - a) - characteristic E x|) torusVolume := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦ by
      rcases characteristic_dichotomy E (x - a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hi).1
    (le_antisymm h (integral_nonneg fun x ↦ abs_nonneg _))
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 (abs_eq_zero.1 hx)

theorem volume_eq_zero_or_one_of_perimeter_zero {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hP : perimeter E = 0) :
    torusVolume E = 0 ∨ torusVolume E = 1 := by
  wlog hEm : MeasurableSet E generalizing E
  · have hae := hE.toMeasurable_ae_eq
    have hP' : perimeter (toMeasurable torusVolume E) = 0 := (perimeter_congr_ae hae).trans hP
    have hh := this (measurableSet_toMeasurable torusVolume E).nullMeasurableSet hP'
      (measurableSet_toMeasurable torusVolume E)
    rwa [measure_congr hae] at hh
  have hall : ∀ᵐ a ∂torusVolume, ∀ᵐ x ∂torusVolume,
      characteristic E (x + a) = characteristic E x := by
    exact Eventually.of_forall fun a ↦ by
      have hh := characteristic_translation_ae_of_perimeter_zero hEm hP (-a)
      filter_upwards [hh] with x hx
      simpa only [sub_neg_eq_add] using hx
  have hswap := (Measure.ae_ae_comm (μ := torusVolume) (ν := torusVolume)
    (p := fun a x ↦ characteristic E (x + a) = characteristic E x)
    (measurableSet_eq_fun ((measurable_characteristic hEm).comp (measurable_snd.add measurable_fst))
      ((measurable_characteristic hEm).comp measurable_snd))).1 hall
  obtain ⟨x, hx⟩ := hswap.exists
  have hav := integral_congr_ae hx
  rw [integral_add_left_eq_self, integral_characteristic hE, integral_const] at hav
  simp only [Measure.real_def, torusVolume_univ, ENNReal.toReal_one, one_smul] at hav
  rcases characteristic_dichotomy E x with h0 | h1
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).1 (hav.trans h0)).resolve_right (measure_ne_top _ _)
  · right
    have hh := congrArg ENNReal.ofReal (hav.trans h1)
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one] using hh

theorem perimeter_pos_of_volume {V : ℝ} (hV : V ∈ Ioo 0 1) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hvolume : torusVolume E = ENNReal.ofReal V) :
    0 < perimeter E := by
  apply bot_lt_iff_ne_bot.2
  intro hzero
  rcases volume_eq_zero_or_one_of_perimeter_zero hE hzero with h0 | h1
  · rw [hvolume] at h0
    exact (ENNReal.ofReal_pos.2 hV.1).ne' h0
  · rw [hvolume] at h1
    have hh := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_ofReal hV.1.le, ENNReal.toReal_one] at hh
    exact hV.2.ne hh

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialCore := by
  exact radialBump.contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport radialCore :=
  radialBump.hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport radialCore ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport (radialBump : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [radialBump.tsupport_eq] at hs
  have hnorm : ‖x - cubeCenter‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans hnorm
  change ‖x i - (1 / 2 : ℝ)‖ ≤ 1 / 3 at hb
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialSquared :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    radialSquared (x + latticeVector n) = radialSquared x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    radialSquared x = 1 - radialBump x * (1 - ‖x - cubeCenter‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    radialSquared x < t ↔ ‖x - cubeCenter‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - cubeCenter)
  have hb0 : 0 ≤ radialBump x := radialBump.nonneg
  have hb1 : radialBump x ≤ 1 := radialBump.le_one
  have he (h : ‖x - cubeCenter‖ ^ 2 < 1 / 16) : radialBump x = 1 := by
    apply radialBump.one_of_mem_closedBall
    change dist x cubeCenter ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - cubeCenter‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - cubeCenter‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion radialSquared (r ^ 2) = cubeBall r := by
  ext z
  change radialSquared (representative z) < r ^ 2 ↔
    dist (representative z) cubeCenter < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

end CubicTorus

namespace CubicTorus

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

lemma cubeBall_eq_metricBall (r : ℝ) :
    cubeBall r = Metric.ball (quotientMap cubeCenter) r := by
  ext x
  change dist (representative x) cubeCenter < r ↔ dist x (quotientMap cubeCenter) < r
  rw [dist_representative_cubeCenter]

lemma localRadialSquared_contDiff (a : Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (localRadialSquared a) :=
  radialSquared_contDiff.comp (contDiff_id.add contDiff_const)

lemma localRadialSquared_periodic (a : Torus) (n : Fin 3 → ℤ) (x : Cover) :
    localRadialSquared a (x + latticeVector n) = localRadialSquared a x := by
  unfold localRadialSquared
  rw [show x + latticeVector n + representative (quotientMap cubeCenter - a) =
    (x + representative (quotientMap cubeCenter - a)) + latticeVector n by abel]
  exact radialSquared_periodic n _

lemma sublevelRegion_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4) :
    sublevelRegion (localRadialSquared a) (r ^ 2) = Metric.ball a r := by
  ext z
  have hrep := periodic_representative radialSquared_periodic
    (representative z + representative (quotientMap cubeCenter - a))
  rw [quotientMap_add, quotientMap_representative, quotientMap_representative] at hrep
  change radialSquared (representative z + representative (quotientMap cubeCenter - a)) < r ^ 2 ↔ _
  rw [← hrep]
  change z + (quotientMap cubeCenter - a) ∈ sublevelRegion radialSquared (r ^ 2) ↔ _
  rw [sublevelRegion_radialSquared hr hs, cubeBall_eq_metricBall]
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show z + (quotientMap cubeCenter - a) - quotientMap cubeCenter = z - a by abel]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_eq_coverTrace (F : Cover → Cover) (x : Cover) :
    divergence F x=coverTrace (fderiv ℝ F x) := rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_denom_pos (v : Cover) :
    0<‖v‖^2+(1-Real.smoothTransition (4*‖v‖^2)) := by
  by_cases h : v=0
  · simp [h]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma regularizedNormal_contDiff {R : Cover → Cover}
    (hR : ContDiff ℝ (⊤ : ℕ∞) R) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedNormal R) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ‖R x‖^2) := hR.norm_sq ℝ
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ ‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))) :=
    hq.add (contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul hq)))
  exact ((hd.sqrt (fun x ↦ (regularizedNormal_denom_pos _).ne')).inv
    (fun x ↦ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)).ne')).smul hR

lemma regularizedNormal_eq {R : Cover → Cover} {x : Cover} (h : (1/4 : ℝ)≤‖R x‖^2) :
    regularizedNormal R x=‖R x‖⁻¹ • R x := by
  unfold regularizedNormal
  rw [Real.smoothTransition.one_of_one_le (by linarith),sub_self,add_zero,
    Real.sqrt_sq (norm_nonneg _)]

lemma regularizedNormal_unit_near {R : Cover → Cover} (hR : Continuous R) {x : Cover}
    (hx : (1/4 : ℝ)<‖R x‖^2) :
    ∀ᶠ y in 𝓝 x,‖regularizedNormal R y‖=1 := by
  have hnear : ∀ᶠ y in 𝓝 x,(1/4 : ℝ)<‖R y‖^2 :=
    (hR.norm.pow 2).continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [hnear] with y hy
  have hn : 0<‖R y‖ := lt_of_not_ge fun h ↦ by
    have hz := le_antisymm h (norm_nonneg _)
    rw [hz] at hy
    norm_num at hy
  rw [regularizedNormal_eq hy.le,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
    inv_mul_cancel₀ hn.ne']

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_boundary_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        ‖N x‖=1 ∧ divergence N x=H) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hs⟩ := isMinimizerAt_global_normal_stability hV hE hmin
  refine ⟨μ,H,N,hμ,hN,hp,?_,?_,hs⟩
  · filter_upwards [hae] with z hz
    exact ⟨hz.1,hz.2.1⟩
  · intro x hx
    constructor
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
        continuous_const (fun m y ↦ by rw [hp]) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hae] with z hz
      rw [hz.1,z.2.property]
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ (continuous_divergence hN)
        continuous_const (divergence_periodic hp) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hae] with z hz
      exact hz.2.2

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_eventuallyEq {N : Cover → Cover} {x : Cover}
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) : regularizedNormal N=ᶠ[𝓝 x]N := by
  filter_upwards [hu] with y hy
  rw [regularizedNormal_eq (by rw [hy]; norm_num),hy,inv_one,one_smul]

namespace Periodic

theorem isMinimizerAt_tubular_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hboundary,hs⟩ := isMinimizerAt_boundary_normal_stability hV hE hmin
  have hR := regularizedNormal_contDiff hN
  have hrp : ∀ m x,regularizedNormal N (x+latticeVector m)=regularizedNormal N x := by
    intro m x
    simp only [regularizedNormal,hp]
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),
      regularizedNormal N=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hae] with z hz
    exact regularizedNormal_eventuallyEq hz.2
  refine ⟨μ,H,regularizedNormal N,hμ,hR,hrp,?_,?_,?_⟩
  · filter_upwards [hae,he] with z hz hze
    exact hze.eq_of_nhds.trans hz.1
  · intro x hx
    refine ⟨regularizedNormal_unit_near hN.continuous (by rw [(hboundary x hx).1]; norm_num),?_⟩
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_divergence hR) (continuous_divergence hN)
      (divergence_periodic hrp) (divergence_periodic hp) _ x hx |>.trans (hboundary x hx).2
    filter_upwards [he] with z hz
    simp only [divergence_eq_coverTrace,hz.fderiv_eq]
  · intro f hf hfp hz
    have hq : normalExtensionJacobi μ f (regularizedNormal N)=normalExtensionJacobi μ f N := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      simp only [hz.fderiv_eq]
    rw [hq]
    exact hs f hf hfp hz

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GraphNormalExtensionDivergence
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

namespace Periodic

theorem isMinimizerAt_curvature_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs⟩ := isMinimizerAt_tubular_normal_stability hV hE hmin
  refine ⟨μ,H,N,hμ,hN,hp,hae,?_,hs⟩
  intro x hx
  exact ⟨(hb x hx).1,(hb x hx).2,
    isMinimizerAt_normal_curvature_nonnegative hV hE hmin hμ hN hp hae x hx (hb x hx).1⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localRadialSquared_lt_iff (a : Torus) (x : Cover) {r : ℝ}
    (hr : 0 ≤ r) (hs : r≤1/4) :
    localRadialSquared a x < r^2 ↔ quotientMap x∈Metric.ball a r := by
  have he := periodic_representative (localRadialSquared_periodic a) x
  rw [← he]
  change quotientMap x∈sublevelRegion (localRadialSquared a) (r^2) ↔ _
  rw [sublevelRegion_localRadialSquared a hr hs]

theorem exists_periodic_local_cutoff (a : Torus) {U : Set Torus}
    (hU : IsOpen U) (ha : a∈U) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧ (∀ x,φ x∈Icc 0 1) ∧
      (∃ W : Set Torus,IsOpen W ∧ a∈W ∧
        ∀ x,quotientMap x∈W → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0 := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min (ε/4) (1/8 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrsmall : 2*r≤1/4 := by dsimp [r]; linarith [min_le_right (ε/4) (1/8 : ℝ)]
  have hrε : 2*r<ε := by dsimp [r]; linarith [min_le_left (ε/4) (1/8 : ℝ)]
  let q := localRadialSquared a
  let φ : Cover → ℝ := fun x ↦ Real.smoothTransition ((r^2-q x)/(r^2/2))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := localRadialSquared_contDiff a
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const _)
  have hden : 0 < r^2/2 := by positivity
  refine ⟨φ,hφ,?_,?_,?_,?_⟩
  · intro m x
    simp only [φ,q,localRadialSquared_periodic]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · refine ⟨Metric.ball a (r/2),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro x hx
    have hxq : q x<(r/2)^2 := (localRadialSquared_lt_iff a x (by positivity) (by linarith)).mpr hx
    have hn : ∀ᶠ y in 𝓝 x,q y < r^2/2 := hq.continuous.continuousAt.eventually_lt_const (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  · intro x hx
    have hnot : quotientMap x∉Metric.ball a (2*r) := fun hh ↦ hx (hεU (Metric.ball_subset_ball hrε.le hh))
    have hxq : (2*r)^2≤q x := le_of_not_gt (fun hh ↦ hnot ((localRadialSquared_lt_iff a x (by positivity) hrsmall).mp hh))
    have hn : ∀ᶠ y in 𝓝 x,r^2<q y := hq.continuous.continuousAt.eventually_const_lt (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_normal_base {F : Cover → ℝ} (hF : Continuous F)
    (μ : FiniteMeasure NormalBundle) :
    Integrable (fun z : NormalBundle ↦ F z.1) (μ : Measure NormalBundle) :=
  (hF.comp normalEmbedding_continuous.fst).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_symm (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q u v=surfaceJacobiB μ q v u := by
  have he : ⟪surfaceMultiplier μ q u.1,v.1⟫=⟪surfaceMultiplier μ q v.1,u.1⟫ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q v.1] with z hu hv
    change (q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hu
    change (q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hv
    change ⟪(q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,v.1 z⟫ =
      ⟪(q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,u.1 z⟫
    rw [hu,hv]
    simp only [smul_eq_mul,Pi.mul_apply,RCLike.inner_apply,RCLike.conj_to_real]
    ring
  unfold surfaceJacobiB
  rw [he,real_inner_comm u.2 v.2]

lemma surfaceJacobiB_add_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v w : SurfaceJet μ) :
    surfaceJacobiB μ q (u+v) w=surfaceJacobiB μ q u w+surfaceJacobiB μ q v w := by
  simp only [surfaceJacobiB,Prod.fst_add,Prod.snd_add,map_add,inner_add_left]
  ring

lemma surfaceJacobiB_smul_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (c : ℝ) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q (c • u) v=c*surfaceJacobiB μ q u v := by
  change ⟪c • u.2,v.2⟫-⟪surfaceMultiplier μ q (c • u.1),v.1⟫ =
    c*(⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫)
  simp only [map_smul,real_inner_smul_left]
  ring

theorem surfaceJacobi_zero_polarizes (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (S : Submodule ℝ (SurfaceJet μ))
    (hs : ∀ u∈S,0 ≤ surfaceJacobiB μ q u u)
    {u : SurfaceJet μ} (hu : u∈S) (hz : surfaceJacobiB μ q u u=0)
    {v : SurfaceJet μ} (hv : v∈S) : surfaceJacobiB μ q u v=0 := by
  have hquad (t : ℝ) : 0≤2*t*surfaceJacobiB μ q u v+t^2*surfaceJacobiB μ q v v := by
    have h := hs (u+t • v) (S.add_mem hu (S.smul_mem t hv))
    rw [surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
      surfaceJacobiB_symm μ q u (u+t • v),surfaceJacobiB_add_left,
      surfaceJacobiB_smul_left,surfaceJacobiB_symm μ q v (u+t • v),
      surfaceJacobiB_add_left,surfaceJacobiB_smul_left,hz,
      surfaceJacobiB_symm μ q v u] at h
    nlinarith only [h]
  by_contra h
  let a := surfaceJacobiB μ q u v
  let b := surfaceJacobiB μ q v v
  have hb : 0≤b := hs v hv
  have hd : 0<b+1 := by linarith
  have hh := hquad (-a/(b+1))
  change 0≤2*(-a/(b+1))*a+(-a/(b+1))^2*b at hh
  have hh' := mul_nonneg hh (sq_nonneg (b+1))
  have he : (2*(-a/(b+1))*a+(-a/(b+1))^2*b)*(b+1)^2= -a^2*(b+2) := by
    field_simp [hd.ne']
    ring
  rw [he] at hh'
  have ha : 0<a^2 := sq_pos_of_ne_zero h
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceSmoothJet_jacobi (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (f : smoothPeriodicScalars) :
    surfaceJacobiB μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f) (surfaceSmoothJet μ f)=
      normalExtensionJacobi μ f.val N := by
  have hf := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hq := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hp := Lp.coeFn_lpSMul (r := 2) (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1
  unfold surfaceJacobiB normalExtensionJacobi
  rw [L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner (surfaceSmoothJet μ f).2 (surfaceSmoothJet μ f).2)
    (L2.integrable_inner (surfaceMultiplier μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1)
      (surfaceSmoothJet μ f).1)]
  apply integral_congr_ae
  filter_upwards [hf,hg,hq,hp] with z hfz hgz hqz hpz
  change ((surfaceSmoothJet μ f).1) z=f.val z.1 at hfz
  change ((surfaceSmoothJet μ f).2) z=_ at hgz
  change (surfaceCurvatureLp μ N hN) z=_ at hqz
  change (surfaceMultiplier μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1) z=_ at hpz
  rw [hpz]
  simp only [smul_eq_mul,Pi.mul_apply,hfz,hqz,hgz,
    real_inner_self_eq_norm_sq,RCLike.inner_apply,RCLike.conj_to_real]
  dsimp [smoothScalarGradient]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceMean_of_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceMean μ (surfaceSmoothJet μ f)=(∫ z,f.val z.1 ∂(μ : Measure NormalBundle)) := by
  change ⟪(ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue smoothScalarOne),
    (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f)⟫=_
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change f.val z.1 * (starRingEnd ℝ) 1=f.val z.1
  simp

lemma surfaceMean_one (μ : FiniteMeasure NormalBundle) :
    surfaceMean μ (surfaceOne μ)=(μ : Measure NormalBundle).real univ := by
  rw [surfaceOne,surfaceMean_of_smooth]
  simp [smoothScalarOne,integral_const,smul_eq_mul]

lemma surfaceOne_mem (μ : FiniteMeasure NormalBundle) : surfaceOne μ∈surfaceH1 μ :=
  subset_closure (LinearMap.mem_range_self _ smoothScalarOne)

lemma continuous_surfaceCenter (μ : FiniteMeasure NormalBundle) : Continuous (surfaceCenter μ) := by
  unfold surfaceCenter
  fun_prop

lemma surfaceMean_center (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0) (u : SurfaceJet μ) :
    surfaceMean μ (surfaceCenter μ u)=0 := by
  simp only [surfaceCenter,map_sub,map_smul,smul_eq_mul,surfaceMean_one]
  field_simp [hm]
  ring

lemma surfaceCenter_mem (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) : surfaceCenter μ u∈surfaceH1 μ :=
  (surfaceH1 μ).sub_mem hu ((surfaceH1 μ).smul_mem _ (surfaceOne_mem μ))

lemma surfaceCenter_of_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceCenter μ (surfaceSmoothJet μ f)=surfaceSmoothJet μ
      (f-(surfaceMean μ (surfaceSmoothJet μ f)/(μ : Measure NormalBundle).real univ) • smoothScalarOne) := by
  rw [map_sub,map_smul]
  rfl

lemma surfaceCenter_eq_self (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : surfaceMean μ u=0) : surfaceCenter μ u=u := by simp [surfaceCenter,hu]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_stability_of_smooth (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hs : ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ m x,f (x+latticeVector m)=f x) →
      (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
      0≤normalExtensionJacobi μ f N)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hz : surfaceMean μ u=0) :
    0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u := by
  let A : Set (SurfaceJet μ) := {v | 0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
    (surfaceCenter μ v) (surfaceCenter μ v)}
  have hc : Continuous (fun v : SurfaceJet μ ↦ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceCenter μ v) (surfaceCenter μ v)) := by
    unfold surfaceJacobiB
    have hcenter := continuous_surfaceCenter μ
    exact (hcenter.snd.inner (𝕜 := ℝ) hcenter.snd).sub
      (((surfaceMultiplier μ (surfaceCurvatureLp μ N hN)).continuous.comp hcenter.fst).inner
        (𝕜 := ℝ) hcenter.fst)
  have hclosed : IsClosed A := isClosed_Ici.preimage hc
  have hrange : Set.range (surfaceSmoothJet μ)⊆A := by
    rintro _ ⟨f,rfl⟩
    change 0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceCenter μ (surfaceSmoothJet μ f)) (surfaceCenter μ (surfaceSmoothJet μ f))
    let g := f-(surfaceMean μ (surfaceSmoothJet μ f)/(μ : Measure NormalBundle).real univ) • smoothScalarOne
    have he : surfaceCenter μ (surfaceSmoothJet μ f)=surfaceSmoothJet μ g := surfaceCenter_of_smooth μ f
    rw [he,surfaceSmoothJet_jacobi]
    apply hs g.val g.property.1 g.property.2
    rw [← surfaceMean_of_smooth,← he,surfaceMean_center μ hm]
  have hmem : u∈closure (Set.range (surfaceSmoothJet μ)) := hu
  have hh := closure_minimal hrange hclosed hmem
  change 0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
    (surfaceCenter μ u) (surfaceCenter μ u) at hh
  rwa [surfaceCenter_eq_self μ hz] at hh

namespace Periodic

theorem isMinimizerAt_H1_trace_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N),
      IsNormalMeasure E μ ∧ (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs⟩ := isMinimizerAt_curvature_stability hV hE hmin
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  exact ⟨μ,H,N,hN,hμ,hp,hae,hb,fun u hu hz ↦ surfaceH1_stability_of_smooth μ hm N hN hs hu hz⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_zero_mode_constant (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0) :
    ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=
      (surfaceJacobiB μ q u (surfaceOne μ)/(μ : Measure NormalBundle).real univ)*surfaceMean μ v := by
  intro v hv
  have hpoly : ∀ w∈surfaceH1ZeroMean μ,0 ≤ surfaceJacobiB μ q w w := by
    intro w hw
    exact hs w hw.1 hw.2
  have hu' : u∈surfaceH1ZeroMean μ := ⟨hu,hmean⟩
  have hw' : surfaceCenter μ v∈surfaceH1ZeroMean μ :=
    ⟨surfaceCenter_mem μ hv,surfaceMean_center μ hm v⟩
  have hp := surfaceJacobi_zero_polarizes μ q (surfaceH1ZeroMean μ) hpoly hu' hz hw'
  have he : v=surfaceCenter μ v+(surfaceMean μ v/(μ : Measure NormalBundle).real univ) • surfaceOne μ := by
    simp [surfaceCenter]
  rw [surfaceJacobiB_symm μ q u v,he,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_symm μ q (surfaceCenter μ v) u,hp,
    surfaceJacobiB_symm μ q (surfaceOne μ) u,zero_add]
  rw [map_add,map_smul,surfaceMean_center μ hm,surfaceMean_one]
  simp only [zero_add,smul_eq_mul]
  field_simp [hm]

theorem surfaceH1_zero_mode_homogeneous (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0)
    {v : SurfaceJet μ} (hv : v∈surfaceH1 μ) (hvmean : surfaceMean μ v≠0)
    (huv : surfaceJacobiB μ q u v=0) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0 := by
  have hc := surfaceH1_zero_mode_constant μ hm q hs hu hmean hz
  have hh := hc v hv
  rw [huv] at hh
  have hz' : surfaceJacobiB μ q u (surfaceOne μ)/(μ : Measure NormalBundle).real univ=0 :=
    (mul_eq_zero.mp hh.symm).resolve_right hvmean
  intro w hw
  rw [hc w hw,hz',zero_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_positive_patch_test {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Torus} (hU : IsOpen U) (ha : (U∩frontier (openRepresentative E)).Nonempty) :
    ∃ f : smoothPeriodicScalars,0 < surfaceMean μ (surfaceSmoothJet μ f) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,f.val y=0 := by
  obtain ⟨a,haU,hab⟩ := ha
  obtain ⟨φ,hφ,hp,hb,⟨W,hW,haW,hone⟩,hzero⟩ := exists_periodic_local_cutoff a hU haU
  let f : smoothPeriodicScalars := ⟨φ,hφ,hp⟩
  refine ⟨f,?_,hzero⟩
  rw [surfaceMean_of_smooth]
  change 0<(∫ z,φ z.1 ∂(μ : Measure NormalBundle))
  by_contra! h
  have hz : (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=0 :=
    le_antisymm h (integral_nonneg fun z ↦ (hb z.1).1)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle ↦ (hb z.1).1)
    (integrable_normal_base hφ.continuous μ)).mp hz
  have he := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous (continuous_const (y := (0 : ℝ))) hp
    (fun _ _ ↦ rfl) hae (representative a) (by simpa only [quotientMap_representative] using hab)
  have hh := (hone (representative a) (by simpa only [quotientMap_representative] using haW)).self_of_nhds
  change φ (representative a)=(0 : ℝ) at he
  linarith

lemma surfaceJacobiB_unused_patch (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ} {U : Set Torus}
    (hu : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0)
    (f : smoothPeriodicScalars)
    (hf : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,f.val y=0) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ f)=0 := by
  have hfv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hfg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hqu := Lp.coeFn_lpSMul (r := 2) q u.1
  have hgrad : ⟪u.2,(surfaceSmoothJet μ f).2⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hu,hfg] with z hz hgz
    by_cases hx : normalProjection z∈U
    · rw [(hz hx).2,inner_zero_left]
      rfl
    · change ((surfaceSmoothJet μ f).2) z=_ at hgz
      rw [hgz]
      have he : f.val=ᶠ[𝓝 (z.1 : Cover)]fun _ ↦ (0 : ℝ) := hf z.1 hx
      have hd := he.fderiv_eq (𝕜 := ℝ)
      have hg : gradient f.val z.1=0 := by simp [gradient,hd]
      change ⟪u.2 z,gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover)⟫=0
      rw [hg]
      simp
  have hval : ⟪surfaceMultiplier μ q u.1,(surfaceSmoothJet μ f).1⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hu,hfv,hqu] with z hz hvz hqz
    change (surfaceMultiplier μ q u.1) z=_ at hqz
    by_cases hx : normalProjection z∈U
    · rw [hqz]
      simp [(hz hx).1]
    · change ((surfaceSmoothJet μ f).1) z=f.val z.1 at hvz
      rw [hvz,(hf z.1 hx).self_of_nhds,inner_zero_right]
      rfl
  simp only [surfaceJacobiB,hgrad,hval,sub_self]

theorem isMinimizerAt_H1_unused_patch_homogeneous {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0) {U : Set Torus}
    (hU : IsOpen U) (ha : (U∩frontier (openRepresentative E)).Nonempty)
    (hzero : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0 := by
  obtain ⟨f,hf,hfg⟩ := isMinimizerAt_positive_patch_test hV hE hmin hμ hU ha
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  exact surfaceH1_zero_mode_homogeneous μ hm q hs hu hmean hz
    (subset_closure (LinearMap.mem_range_self _ f)) hf.ne'
    (surfaceJacobiB_unused_patch μ q hzero f hfg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalComponentScalar_mean_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 := by
  let e : Cover := EuclideanSpace.single i 1
  have he : ‖e‖=1 := by simp [e]
  have hF : AdmissibleField (fun _ : Cover ↦ e) := ⟨contDiff_const,fun _ _ ↦ rfl,fun _ ↦ he.le⟩
  have hflux := hμ.2 _ hF
  have hd : divergence (fun _ : Cover ↦ e)=fun _ ↦ 0 := by funext x; simp [divergence]
  rw [hd,integral_zero] at hflux
  rw [surfaceMean_of_smooth,← hflux]
  apply integral_congr_ae
  filter_upwards [hae] with z hz
  change ⟪e,N z.1⟫=⟪(z.2 : Cover),e⟫
  rw [hz,real_inner_comm]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_NormalCurvatureScalar
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_H1_jacobi_system {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N),
      IsNormalMeasure E μ ∧ (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ (u : SurfaceJet μ),u∈surfaceH1 μ → surfaceMean μ u=0 →
        surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 →
        ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
        (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) →
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) := by
  obtain ⟨μ,H,N,hN,hμ,hp,hae,hb,hs⟩ := isMinimizerAt_H1_trace_stability hV hE hmin
  refine ⟨μ,H,N,hN,hμ,hp,hae,hb,hs,?_⟩
  intro u hu hm hz U hU ha hzero
  exact isMinimizerAt_H1_unused_patch_homogeneous hV hE hmin hμ
    (surfaceCurvatureLp μ N hN) hs hu hm hz hU ha hzero

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_H1_translation_jacobi_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N)
      (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ i : Fin 3,surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 ∧
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
          (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) ∧
      (∀ (u : SurfaceJet μ),u∈surfaceH1 μ → surfaceMean μ u=0 →
        surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 →
        ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
        (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) →
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) := by
  obtain ⟨μ,H,N,hN,hμ,hp,hae,hb,hs,hunused⟩ := isMinimizerAt_H1_jacobi_system hV hE hmin
  refine ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,?_,hunused⟩
  intro i
  exact ⟨normalComponentScalar_mean_zero hμ hN hp hae i,
    normalComponentScalar_global_jacobi hV hE hmin hμ hN hp hae (fun x hx ↦ (hb x hx).1) hs i⟩

end Periodic
end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi_oai := @OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi_oai
