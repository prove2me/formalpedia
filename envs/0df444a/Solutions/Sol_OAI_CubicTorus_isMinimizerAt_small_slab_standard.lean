-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_small_slab_standard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:08:37.176273+00:00
-- url     : https://prove2.me/submissions/2598523a-7fbb-4156-91c8-7772473de66e

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_standard_slab
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_exact_profile_hessian
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_connected_curvature_integral_pos
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_four_corner_necessary_data
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_second_endpoint_linear_bound
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_second_transition_nonstandard_star
import Theorems.Thm_OAI_CubicTorus_isoperimetricProfile_slab_local_min
import Theorems.Thm_OAI_CubicTorus_secondCorner_endpoint_contradiction

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

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

theorem finitePerimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    FinitePerimeter E ↔ FinitePerimeter F := by
  rw [FinitePerimeter, FinitePerimeter, perimeter_congr_ae hEF]
  exact and_congr ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩ Iff.rfl

theorem isMinimizerAt_congr_ae {E F : Set Torus} {V : ℝ}
    (hEF : E =ᵐ[torusVolume] F) : IsMinimizerAt V E ↔ IsMinimizerAt V F := by
  unfold IsMinimizerAt
  rw [finitePerimeter_congr_ae hEF, measure_congr hEF, perimeter_congr_ae hEF]

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integrableOn_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IntegrableOn (divergence F) fundamentalCube := by
  have hEmb := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_comp_preimage hEmb]
  rw [cube_preimage]
  have hc : Continuous (fun x : Fin 3 → ℝ => divergence F (WithLp.toLp 2 x)) :=
    (continuous_divergence hF).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => le_of_lt (hx i (mem_univ i)).2⟩

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

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

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

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma divergence_smul_function {f : Cover → ℝ} {F : Cover → Cover} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (hF : DifferentiableAt ℝ F point) :
    divergence (fun y ↦ f y • F y) point = f point * divergence F point +
      ⟪gradient f point, F point⟫ := by
  have ha : (∑ i : Fin 3, F point i • EuclideanSpace.single i 1) = F point := by
    ext j
    simp [Pi.single_apply]
  rw [inner_gradient_left]
  conv_rhs => rw [← ha, map_sum]
  change (∑ i : Fin 3, (fderiv ℝ (f • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_smul hf hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    divergence, Finset.mul_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
open scoped RealInnerProductSpace

lemma normalMeasure_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    (∫ z, normalTest F hF.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  have hG : AdmissibleField (fun x ↦ k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hk.le)).trans_eq
        (inv_mul_cancel₀ hk.ne')
  have hh := hμ.2 _ hG
  simp only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right,
    integral_const_mul] at hh ⊢
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_ne_zero hk.ne') hh

end CubicTorus

open scoped RealInnerProductSpace

namespace CubicTorus
open Filter
open scoped Topology

lemma coordinateMove_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateMove i f t) := by
  unfold coordinateMove
  fun_prop

lemma coordinateMove_hasFDerivAt (i : Fin 3) {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (t : ℝ) :
    HasFDerivAt (coordinateMove i f t) (coordinateMoveDeriv i f t point) point := by
  have h₁ : HasFDerivAt (fun y : Cover ↦ y) (ContinuousLinearMap.id ℝ Cover) point :=
    hasFDerivAt_id point
  have h₂ := (hf.hasFDerivAt.const_mul t).smul_const
    (EuclideanSpace.single i (1 : ℝ) : Cover)
  have he : coordinateMoveDeriv i f t point = ContinuousLinearMap.id ℝ Cover +
      (t • fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ) : Cover) := by
    ext y j
    simp [coordinateMoveDeriv, mul_comm]
  rw [he]
  exact h₁.add h₂

lemma coordinateMove_periodic (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (t : ℝ) (n : Fin 3 → ℤ) (x : Cover) :
    coordinateMove i f t (x + latticeVector n) = coordinateMove i f t x + latticeVector n := by
  simp only [coordinateMove, hp]
  abel

lemma coordinateMoveDeriv_det (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) :
    (coordinateMoveDeriv i f t x).det = coordinateJacobian i f t x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (coordinateMoveDeriv i f t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) +
        (if j = i then t * fderiv ℝ f x (EuclideanSpace.single k 1) else 0)) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (coordinateMoveDeriv i f t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    by_cases h : j = i <;> simp [coordinateMoveDeriv, h, mul_comm]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  rw [Matrix.det_fin_three]
  fin_cases i <;> simp [coordinateJacobian]

lemma coordinateMove_injective (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) : Function.Injective (coordinateMove i f t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = -(t * (f x - f y)) • EuclideanSpace.single i 1 := by
    calc
      x - y = coordinateMove i f t x - coordinateMove i f t y -
          (t * (f x - f y)) • EuclideanSpace.single i 1 := by
        unfold coordinateMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖f x - f y‖ := by
    rw [he, norm_smul, norm_neg, Real.norm_eq_abs, abs_mul]
    simp [Real.norm_eq_abs]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    have hz := hLip.norm_sub_le x y
    calc
      ‖x - y‖ = |t| * ‖f x - f y‖ := hn
      _ ≤ |t| * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by ring
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma divergence_sub_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y - G y) point = divergence F point - divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F - G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_sub hF hG]
  simp [divergence, Finset.sum_sub_distrib]

lemma linearForm_apply_basis (L : Cover →L[ℝ] ℝ) (v : Cover) :
    L v = ∑ j : Fin 3, v j * L (EuclideanSpace.single j 1) := by
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j 1) = v := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hv, map_sum]
  simp

lemma divergence_comp_coordinateMove (i : Fin 3) {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) {G : Cover → Cover} {time : ℝ}
    (hG : DifferentiableAt ℝ G (coordinateMove i f time point)) :
    divergence (fun y ↦ G (coordinateMove i f time y)) point =
      divergence G (coordinateMove i f time point) +
        time * fderiv ℝ f point
          (fderiv ℝ G (coordinateMove i f time point) (EuclideanSpace.single i 1)) := by
  have hm := coordinateMove_hasFDerivAt i hf time
  have hd := (hG.hasFDerivAt.comp point hm).fderiv
  change fderiv ℝ (fun y ↦ G (coordinateMove i f time y)) point = _ at hd
  simp only [divergence, hd,
    coordinateMoveDeriv, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateJacobian_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateJacobian i f t) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  unfold coordinateJacobian
  fun_prop

lemma coordinatePullback_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinatePullback i f t G) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hm := coordinateMove_contDiff i hf t
  have hj := coordinateJacobian_contDiff i hf t
  unfold coordinatePullback
  exact (hj.smul (hG.comp hm)).sub
    ((contDiff_const.mul (hd.clm_apply (hG.comp hm))).smul contDiff_const)

lemma coordinatePullback_periodic (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ n x, G (x + latticeVector n) = G x) (n : Fin 3 → ℤ) (x : Cover) :
    coordinatePullback i f t G (x + latticeVector n) = coordinatePullback i f t G x := by
  simp only [coordinatePullback, coordinateJacobian, fderiv_periodic hp,
    coordinateMove_periodic i hp, hG]

lemma coordinatePullback_divergence (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (coordinatePullback i f t G) x =
      coordinateJacobian i f t x * divergence G (coordinateMove i f t x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := coordinateMove_hasFDerivAt i hfd t
  have hg := (hG.differentiable (by simp)).differentiableAt (x := coordinateMove i f t x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := ((hdf.hasFDerivAt.clm_apply (hasFDerivAt_const
    (EuclideanSpace.single i (1 : ℝ) : Cover) x)).const_mul t).const_add 1
  have hb := (hdf.hasFDerivAt.clm_apply hu).const_mul t
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top))
    (EuclideanSpace.single i 1) (G (coordinateMove i f t x))
  change divergence (fun y ↦ coordinateJacobian i f t y • G (coordinateMove i f t y) -
    (t * fderiv ℝ f y (G (coordinateMove i f t y))) • EuclideanSpace.single i 1) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (coordinateJacobian i f t) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (coordinateJacobian i f t) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ G (coordinateMove i f t y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ
      (fun y ↦ t * fderiv ℝ f y (G (coordinateMove i f t y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ coordinateJacobian i f t y • G (coordinateMove i f t y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ (t * fderiv ℝ f y (G (coordinateMove i f t y))) •
        (EuclideanSpace.single i 1 : Cover)) x := hB.smul_const _
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU,
    divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_coordinateMove i hfd hg]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, zero_add,
    coordinateMoveDeriv, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero]
  dsimp only [coordinateJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

namespace CubicTorus

lemma coordinateJacobian_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) (x : Cover) :
    ‖coordinateJacobian i f t x‖ ≤ 1 + |t| * M := by
  have hd : ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ M := by
    simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (EuclideanSpace.single i 1)).trans
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  calc
    _ ≤ ‖(1 : ℝ)‖ + ‖t * fderiv ℝ f x (EuclideanSpace.single i 1)‖ := norm_add_le _ _
    _ ≤ 1 + |t| * M := by
      rw [norm_one, norm_mul, Real.norm_eq_abs t]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) 1

lemma coordinateJacobian_pos (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) {t : ℝ} (ht : |t| * M < 1) (x : Cover) :
    0 < coordinateJacobian i f t x := by
  have hd : |fderiv ℝ f x (EuclideanSpace.single i 1)| ≤ M := by
    simpa [Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (EuclideanSpace.single i 1)).trans
        (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left hd (abs_nonneg t)
  rw [← abs_mul] at hb
  have := (abs_le.1 hb).1
  unfold coordinateJacobian
  linarith

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
namespace CubicTorus

lemma coordinatePullback_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ x, ‖G x‖ ≤ 1) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ 1 + 2 * |t| * M := by
  have hu := hG (coordinateMove i f t x)
  have hd : ‖fderiv ℝ f x (G (coordinateMove i f t x))‖ ≤ M :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [hM x, norm_nonneg (fderiv ℝ f x)])
  calc
    _ ≤ ‖coordinateJacobian i f t x • G (coordinateMove i f t x)‖ +
        ‖(t * fderiv ℝ f x (G (coordinateMove i f t x))) • EuclideanSpace.single i 1‖ :=
      norm_sub_le _ _
    _ ≤ (1 + |t| * M) + |t| * M := by
      simp only [norm_smul, norm_mul]
      have he : ‖(EuclideanSpace.single i (1 : ℝ) : Cover)‖ = 1 := by simp
      rw [he, mul_one, Real.norm_eq_abs t]
      exact add_le_add
        (by simpa only [mul_one] using
          (mul_le_mul (coordinateJacobian_norm_le i hM t x) hu
            (norm_nonneg _) (by positivity)))
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

end CubicTorus

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma inner_coordinatePullback (i : Fin 3) (f : Cover → ℝ) (t : ℝ)
    (G : Cover → Cover) (x n : Cover) :
    ⟪n, coordinatePullback i f t G x⟫ =
      ⟪coordinateCofactor i f t x n, G (coordinateMove i f t x)⟫ := by
  simp only [coordinatePullback, coordinateCofactor, inner_sub_right, real_inner_smul_right,
    inner_sub_left, real_inner_smul_left, inner_gradient_left]
  ring

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinateCofactor_eq (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x n : Cover) :
    coordinateCofactor i f t x n = n + t • coordinateNormalVelocity i f x n := by
  unfold coordinateCofactor coordinateJacobian coordinateNormalVelocity
  module

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_directionalDeriv (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) :=
    hf.smul contDiff_const
  have hi := integrableOn_divergence hFc
  have he : divergence (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) =
      fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact divergence_smul_const (hf.differentiable (by simp)).differentiableAt _
  rwa [he] at hi

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinatePullback_smul (i : Fin 3) (f : Cover → ℝ) (t c : ℝ)
    (F : Cover → Cover) (x : Cover) :
    coordinatePullback i f t (fun y ↦ c • F y) x = c • coordinatePullback i f t F x := by
  simp only [coordinatePullback, map_smul, smul_sub, smul_smul]
  module

lemma coordinatePullback_norm_le_mul (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    {k : ℝ} (hk : 0 < k) (hG : ∀ x, ‖G x‖ ≤ k) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ (1 + 2 * |t| * M) * k := by
  have hnorm : ∀ y, ‖k⁻¹ • G y‖ ≤ 1 := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
    exact (mul_le_mul_of_nonneg_left (hG y) (inv_nonneg.mpr hk.le)).trans_eq
      (inv_mul_cancel₀ hk.ne')
  have hh := coordinatePullback_norm_le i hM0 hM t hnorm x
  rw [coordinatePullback_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hk.le)] at hh
  calc
    _ = k * (k⁻¹ * ‖coordinatePullback i f t G x‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ k * (1 + 2 * |t| * M) := mul_le_mul_of_nonneg_left hh hk.le
    _ = _ := mul_comm _ _

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

lemma flux_sum_components (E : Set Torus) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) =
      ∑ i : Fin 3, directionalFlux E i (fun x ↦ F x i) := by
  unfold divergence directionalFlux
  simp_rw [← fderiv_component (hF.differentiable (by simp)).differentiableAt]
  exact integral_finsetSum _ (fun i _ ↦
    (integrableOn_directionalDeriv i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)).mono_set
      inter_subset_left)

lemma exists_positive_directionalFlux {E : Set Torus} (hP : 0 < perimeter E) :
    ∃ (i : Fin 3) (f : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ n x, f (x + latticeVector n) = f x) ∧ 0 < directionalFlux E i f := by
  have hh : ∃ F, AdmissibleField F ∧
      0 < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    by_contra! hn
    have : perimeter E ≤ 0 := iSup_le fun F ↦ iSup_le fun hF ↦ by
      exact (ENNReal.ofReal_eq_zero.2 (hn F hF)).le
    exact not_le_of_gt hP this
  obtain ⟨F, hF, hp⟩ := hh
  rw [flux_sum_components E hF.1] at hp
  have hi : ∃ i : Fin 3, 0 < directionalFlux E i (fun x ↦ F x i) := by
    by_contra! hn
    exact not_le_of_gt hp (Finset.sum_nonpos fun i _ ↦ hn i)
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, fun x ↦ F x i, (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF.1, ?_, hi⟩
  intro n x
  dsimp only
  rw [hF.2.1]

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

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
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
open scoped ENNReal NNReal Topology Pointwise
namespace CubicTorus

lemma latticeVector_injective : Function.Injective latticeVector := by
  intro n m h
  funext i
  have hi := congrArg (fun x : Cover ↦ x i) h
  change (n i : ℝ)=(m i : ℝ) at hi
  exact_mod_cast hi

lemma lattice_fundamentalCube : IsAddFundamentalDomain (Fin 3 → ℤ) fundamentalCube volume := by
  apply IsAddFundamentalDomain.mk' measurableSet_fundamentalCube.nullMeasurableSet
  intro x
  obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  refine ⟨n,?_,?_⟩
  · change x+latticeVector n∈fundamentalCube
    rw [← hn]
    exact representative_mem_fundamentalCube _
  · intro m hm
    change x+latticeVector m∈fundamentalCube at hm
    have hq : quotientMap (x+latticeVector m)=quotientMap x := by
      rw [quotientMap_add,quotientMap_latticeVector,add_zero]
    have he : x+latticeVector m=x+latticeVector n := by
      rw [← hn,← hq,representative_quotientMap_of_mem hm]
    exact latticeVector_injective (add_left_cancel he)

lemma periodic_image_fundamental {T : Cover → Cover} (hc : Continuous T)
    (hb : Function.Bijective T)
    (hp : ∀ n x,T (x+latticeVector n)=T x+latticeVector n) :
    IsAddFundamentalDomain (Fin 3 → ℤ) (T '' fundamentalCube) volume := by
  apply IsAddFundamentalDomain.mk'
    ((hc.measurableEmbedding hb.1).measurableSet_image' measurableSet_fundamentalCube).nullMeasurableSet
  intro y
  obtain ⟨x,rfl⟩ := hb.2 y
  obtain ⟨n,hn,huniq⟩ : ∃! n : Fin 3 → ℤ,x+latticeVector n∈fundamentalCube := by
    obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
    refine ⟨n,?_,?_⟩
    · dsimp only; rw [← hn]; exact representative_mem_fundamentalCube _
    · intro m hm
      apply latticeVector_injective
      apply add_left_cancel (a:=x)
      rw [← hn,← (show quotientMap (x+latticeVector m)=quotientMap x by
        rw [quotientMap_add,quotientMap_latticeVector,add_zero]),representative_quotientMap_of_mem hm]
  refine ⟨n,?_,?_⟩
  · change T x+latticeVector n∈T '' fundamentalCube
    exact ⟨x+latticeVector n,hn,hp n x⟩
  · intro m hm
    obtain ⟨z,hz,hzm⟩ := hm
    exact huniq m (by dsimp only; have he : z=x+latticeVector m := hb.1 (hzm.trans (hp m x).symm); rwa [← he])

lemma integral_periodic_image_cube {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {T : Cover → Cover} (hc : Continuous T) (hb : Function.Bijective T)
    (hp : ∀ n x,T (x+latticeVector n)=T x+latticeVector n)
    {g : Cover → Y} (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube,g x) = ∫ x in T '' fundamentalCube,g x :=
  lattice_fundamentalCube.setIntegral_eq (periodic_image_fundamental hc hb hp) hg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateMove_surjective (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M)
    {t : ℝ} (ht : |t| *M<1) : Function.Surjective (coordinateMove i f t) := by
  intro y
  let g : Cover → Cover := fun x ↦ y-(t*f x) • EuclideanSpace.single i 1
  have hg : ContractingWith (‖t‖₊*M) g := by
    refine ⟨by exact_mod_cast ht, LipschitzWith.of_dist_le_mul ?_⟩
    intro x z
    have he : g x-g z=(-(t*(f x-f z))) • EuclideanSpace.single i 1 := by dsimp [g]; module
    rw [dist_eq_norm,he,norm_smul]
    simp only [norm_neg,Real.norm_eq_abs,abs_mul,PiLp.norm_single,norm_one,mul_one,
      NNReal.coe_mul,coe_nnnorm]
    calc
      |t| * |f x-f z| ≤ |t| *(M*dist x z) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using
          (lipschitzWith_of_nnnorm_fderiv_le hf hM).dist_le_mul x z) (abs_nonneg t)
      _ = _ := by ring
  refine ⟨hg.fixedPoint,?_⟩
  have he := hg.fixedPoint_isFixedPt
  change y-(t*f hg.fixedPoint) • EuclideanSpace.single i 1=hg.fixedPoint at he
  exact eq_sub_iff_add_eq.mp he.symm

lemma periodicCoordinateRegion_measurable (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M)
    {t : ℝ} (ht : |t| *M<1) {E : Set Torus} (hE : MeasurableSet E) :
    MeasurableSet (periodicCoordinateRegion i f t E) := by
  have hc : Continuous (coordinateMove i f t) := continuous_id.add
    ((continuous_const.mul hf.continuous).smul continuous_const)
  exact ((hc.measurableEmbedding (coordinateMove_injective i hf hM ht)).measurableSet_image'
    (measurable_quotientMap hE)).preimage measurable_representative

lemma periodicCoordinateRegion_lift (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x,f (x+latticeVector n)=f x) (t : ℝ) (E : Set Torus) :
    quotientMap ⁻¹' periodicCoordinateRegion i f t E=coordinateMove i f t '' (quotientMap ⁻¹' E) := by
  ext x
  have hind : ∀ n y, (y+latticeVector n∈coordinateMove i f t '' (quotientMap ⁻¹' E)) ↔
      y∈coordinateMove i f t '' (quotientMap ⁻¹' E) := by
    intro n y
    constructor
    · rintro ⟨z,hz,he⟩
      refine ⟨z+latticeVector (-n),?_,?_⟩
      · change quotientMap (z+latticeVector (-n))∈E
        simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hz
      · rw [coordinateMove_periodic i hp,he]
        ext j; simp [latticeVector]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨z+latticeVector n,?_,coordinateMove_periodic i hp t n z⟩
      simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hz
  change representative (quotientMap x)∈coordinateMove i f t '' (quotientMap ⁻¹' E) ↔
    x∈coordinateMove i f t '' (quotientMap ⁻¹' E)
  obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  rw [hn,hind]

lemma integral_periodicCoordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) (hp : ∀ n x,f (x+latticeVector n)=f x)
    {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M) {t : ℝ} (ht : |t| *M<1)
    {E : Set Torus} (hE : MeasurableSet E) {g : Cover → ℝ}
    (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' periodicCoordinateRegion i f t E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
        coordinateJacobian i f t x*g (coordinateMove i f t x) := by
  let S := quotientMap ⁻¹' periodicCoordinateRegion i f t E
  have hS : MeasurableSet S := measurable_quotientMap (periodicCoordinateRegion_measurable i hf hM ht hE)
  have hsp : ∀ n x,S.indicator g (x+latticeVector n)=S.indicator g x := by
    intro n x
    by_cases hx : x∈S
    · have hx' : x+latticeVector n∈S := by
        simpa only [S,mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hx
      simp only [indicator_of_mem hx,indicator_of_mem hx',hg]
    · have hx' : x+latticeVector n∉S := by
        simpa only [S,mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hx
      simp only [indicator_of_notMem hx,indicator_of_notMem hx']
  have hc : Continuous (coordinateMove i f t) := continuous_id.add
    ((continuous_const.mul hf.continuous).smul continuous_const)
  have he := integral_periodic_image_cube hc
    ⟨coordinateMove_injective i hf hM ht,coordinateMove_surjective i hf hM ht⟩
    (coordinateMove_periodic i hp t) hsp
  rw [integral_indicator hS,integral_indicator hS] at he
  simp only [Measure.restrict_restrict hS,inter_comm S] at he
  change (∫ x in fundamentalCube∩S,g x)=_
  rw [he]
  have him : coordinateMove i f t '' fundamentalCube∩S=
      coordinateMove i f t '' (fundamentalCube∩quotientMap ⁻¹' E) := by
    dsimp only [S]
    rw [periodicCoordinateRegion_lift i hp]
    exact (Set.image_inter (coordinateMove_injective i hf hM ht)).symm
  rw [him,integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE))
    (fun x _ ↦ (coordinateMove_hasFDerivAt i (hf x) t).hasFDerivWithinAt)
    (coordinateMove_injective i hf hM ht).injOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [coordinateMoveDeriv_det,abs_of_pos (coordinateJacobian_pos i
    (fun y ↦ by exact_mod_cast hM y) ht x),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma perimeter_periodicCoordinateRegion_le (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    perimeter (periodicCoordinateRegion i f t E) ≤
      ENNReal.ofReal (1 + 2 * |t| * M) * perimeter E := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter at ⊢
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_periodicCoordinateRegion i hfd hp hM ht hE (divergence_periodic hG.2.1)]
  have hh := abs_flux_le_mul_perimeter hP
    (coordinatePullback_contDiff i hf t hG.1) (coordinatePullback_periodic i hp t hG.2.1)
    hC (coordinatePullback_norm_le i M.coe_nonneg hMr t hG.2.2)
  simp_rw [coordinatePullback_divergence i hf t hG.1] at hh
  calc
    _ ≤ ENNReal.ofReal ((1 + 2 * |t| * M) * (perimeter E).toReal) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hh)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hP]
      rfl

lemma finitePerimeter_periodicCoordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) : FinitePerimeter (periodicCoordinateRegion i f t E) := by
  refine ⟨(periodicCoordinateRegion_measurable i (hf.differentiable (by simp)) hM ht hE).nullMeasurableSet,
    (perimeter_periodicCoordinateRegion_le i hf hp hM ht hE hP).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top

namespace Periodic

lemma exists_variation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x,f (x+latticeVector n)=f x) :
    ∃ a : Variation,a.coordinate=i ∧ a.function=f := by
  obtain ⟨M,hM,hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨i,f,⟨M,hM⟩,hf,hp,fun x ↦ by exact_mod_cast hbound x⟩,rfl,rfl⟩

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

lemma chainBound_pos (l : VariationChain) : 0 < chainBound l := by
  induction l with
  | nil => norm_num [chainBound]
  | cons p l ih => rcases p with ⟨a,t⟩; exact mul_pos (by positivity) ih

lemma chainMove_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainMove l) := by
  induction l with
  | nil => exact contDiff_id
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih.comp (coordinateMove_contDiff a.coordinate a.smooth t)

lemma chainJacobian_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainJacobian l) := by
  induction l with
  | nil => exact contDiff_const
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact (coordinateJacobian_contDiff a.coordinate a.smooth t).mul
      (ih.comp (coordinateMove_contDiff a.coordinate a.smooth t))

lemma chainPullback_contDiff (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (chainPullback l F) := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_contDiff a.coordinate a.smooth t ih

lemma chainPullback_periodic (l : VariationChain) {F : Cover → Cover}
    (hF : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,chainPullback l F (x+latticeVector n)=chainPullback l F x := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_periodic a.coordinate a.periodic t ih

lemma chainPullback_norm (l : VariationChain) {F : Cover → Cover} (hF : ∀ x,‖F x‖≤1) :
    ∀ x,‖chainPullback l F x‖ ≤ chainBound l := by
  induction l with
  | nil => exact hF
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact coordinatePullback_norm_le_mul a.coordinate a.bound.coe_nonneg
      (fun x ↦ by exact_mod_cast a.derivative_bound x) t (chainBound_pos l) ih

lemma chainPullback_divergence (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (chainPullback l F) x = chainJacobian l x * divergence F (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainPullback,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,coordinatePullback_divergence a.coordinate a.smooth t (chainPullback_contDiff l hF),ih]
    simp only [chainJacobian,chainMove,mul_assoc]

lemma chain_inner_pullback (l : VariationChain) (F : Cover → Cover) (x n : Cover) :
    ⟪n,chainPullback l F x⟫=⟪chainCofactor l x n,F (chainMove l x)⟫ := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,inner_coordinatePullback,ih]
    rfl

lemma chainRegion_measurable {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : MeasurableSet (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact hE
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp))
        a.derivative_bound (hl (a,t) (by simp)) hE)

lemma chainRegion_finite {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) (hfin : perimeter E<⊤) : FinitePerimeter (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact ⟨hE.nullMeasurableSet,hfin⟩
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE)
      (finitePerimeter_periodicCoordinateRegion a.coordinate a.smooth a.periodic a.derivative_bound ht hE hfin.ne).2

lemma chainMove_periodic (l : VariationChain) (n : Fin 3 → ℤ) (x : Cover) :
    chainMove l (x+latticeVector n)=chainMove l x+latticeVector n := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainMove,coordinateMove_periodic a.coordinate a.periodic,ih]
    rfl

lemma chainJacobian_periodic (l : VariationChain) (n : Fin 3 → ℤ) (x : Cover) :
    chainJacobian l (x+latticeVector n)=chainJacobian l x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [chainJacobian,coordinateMove_periodic a.coordinate a.periodic,ih,
      coordinateJacobian,fderiv_periodic a.periodic]

lemma integral_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {g : Cover → ℝ}
    (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x*g (chainMove l x) := by
  induction l generalizing E with
  | nil => simp [chainRegion,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    rw [chainRegion,ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE),
      integral_periodicCoordinateRegion a.coordinate (a.smooth.differentiable (by simp))
        a.periodic a.derivative_bound ht hE (fun n x ↦ by
          rw [chainJacobian_periodic,chainMove_periodic,hg])]
    simp only [chainJacobian,chainMove,mul_assoc]

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
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

lemma integrableOn_fundamentalCube_of_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Cover → F} (hf : Continuous f) : IntegrableOn f fundamentalCube :=
  (hf.continuousOn.integrableOn_compact isCompact_closedFundamentalCube).mono_set
    (fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma wallVelocity_contDiff (a : Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2) := by
  unfold coordinateNormalVelocity
  exact (((a.smooth.fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_const).smul contDiff_snd |>.sub
    ((contDiff_snd.inner ℝ contDiff_const).smul ((gradient_contDiff a.smooth).comp contDiff_fst))

lemma chainCofactor_contDiff (l : VariationChain) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦ chainCofactor l p.1 p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦
        coordinateCofactor a.coordinate a.function t p.1 p.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.add (contDiff_const.fun_smul (wallVelocity_contDiff a))
    exact ih.comp (((coordinateMove_contDiff a.coordinate a.smooth t).comp contDiff_fst).prodMk hc)

lemma chainCofactor_continuous_normal (l : VariationChain) :
    Continuous (fun z : NormalBundle ↦ chainCofactor l z.1 z.2) :=
  (chainCofactor_contDiff l).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

theorem perimeter_chainRegion_le_normalArea {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) : perimeter (chainRegion l E)≤ENNReal.ofReal
      (∫ z,‖chainCofactor l z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  have hΓ := chainPullback_contDiff l hF.1
  have hflux := normalMeasure_flux hμ hΓ (chainPullback_periodic l hF.2.1)
    (chainBound_pos l) (chainPullback_norm l hF.2.2)
  rw [integral_chainRegion hl hE (divergence_periodic hF.2.1)]
  simp_rw [← chainPullback_divergence l hF.1]
  rw [← hflux]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ hΓ.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (chainCofactor_continuous_normal l).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),chainPullback l F z.1⟫≤_
    rw [chain_inner_pullback]
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 _))

lemma chainJacobian_append (l k : VariationChain) (x : Cover) :
    chainJacobian (l++k) x=chainJacobian l x*chainJacobian k (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [List.cons_append,chainJacobian,chainMove,ih,mul_assoc]

lemma chainCofactor_append (l k : VariationChain) (x n : Cover) :
    chainCofactor (l++k) x n=chainCofactor k (chainMove l x) (chainCofactor l x n) := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _ _

lemma ChainValid.append {l k : VariationChain} (hl : ChainValid l) (hk : ChainValid k) :
    ChainValid (l++k) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hl p hp
  · exact hk p hp

lemma volume_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : torusVolume.real (chainRegion l E)=chainMass l E := by
  rw [realVolume_lift (chainRegion_measurable hl hE)]
  rw [← setIntegral_one_eq_measureReal]
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,(1 : ℝ))=_
  rw [integral_chainRegion hl hE (fun _ _ ↦ rfl)]
  simp only [mul_one,chainMass]

lemma chainMass_append (l : VariationChain) (b : Variation) (s : ℝ) (E : Set Torus) :
    chainMass (l++[(b,s)]) E=chainMass l E+s*chainTransportedFlux l b E := by
  have hJ := integrableOn_fundamentalCube_of_continuous (chainJacobian_contDiff l).continuous
  have hB : IntegrableOn (fun x ↦ chainJacobian l x*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) fundamentalCube :=
    integrableOn_fundamentalCube_of_continuous
    ((chainJacobian_contDiff l).continuous.mul
      ((((b.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp (chainMove_contDiff l).continuous)))
  unfold chainMass chainTransportedFlux
  simp only [chainJacobian_append,chainJacobian,coordinateJacobian,mul_one]
  simp_rw [mul_add,mul_one,show ∀ x : Cover,chainJacobian l x*(s*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1))=
      s*(chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) from fun x ↦ by ring]
  rw [integral_add (hJ.mono_set inter_subset_left) ((hB.mono_set inter_subset_left).const_mul s),integral_const_mul]

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

lemma simultaneousMove_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainMove (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    exact ih.comp (contDiff_fst.prodMk hm)

lemma simultaneousJacobian_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_const
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateJacobian a.coordinate a.function p.1 p.2) := by
      unfold coordinateJacobian
      exact contDiff_const.add (contDiff_fst.mul (((a.smooth.fderiv_right (by simp)).comp contDiff_snd).clm_apply contDiff_const))
    exact hJ.mul (ih.comp (contDiff_fst.prodMk hm))

lemma simultaneousCofactor_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2) := by
  induction l with
  | nil => exact contDiff_snd.snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateMove a.coordinate a.function p.1 p.2.1) := by
      unfold coordinateMove
      exact contDiff_snd.fst.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd.fst)).smul contDiff_const)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateCofactor a.coordinate a.function p.1 p.2.1 p.2.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.snd.add (contDiff_fst.fun_smul ((wallVelocity_contDiff a).comp contDiff_snd))
    exact ih.comp (contDiff_fst.prodMk (hm.prodMk hc))

@[simp] lemma simultaneousCofactor_zero (l : List Variation) (x n : Cover) :
    chainCofactor (simultaneousChain l 0) x n=n := by
  induction l generalizing x n with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainCofactor,coordinateCofactor_eq,coordinateMove] using ih x n

lemma simultaneousChain_eventually_valid (l : List Variation) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t) := by
  induction l with
  | nil => exact Eventually.of_forall fun _ p hp ↦ by simp [simultaneousChain] at hp
  | cons a l ih =>
    have ha : ∀ᶠ t in 𝓝 (0 : ℝ),|t| *(a.bound : ℝ)<1 :=
      (continuous_abs.mul continuous_const).continuousAt.eventually (eventually_lt_nhds (by simp))
    filter_upwards [ih,ha] with t ht hat
    intro p hp
    simp only [simultaneousChain,List.map_cons,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact hat
    · exact ht p hp

@[simp] lemma simultaneousMass_zero (l : List Variation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure X} [IsFiniteMeasure μ]

omit [NormedSpace ℝ X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_of_continuous_compact_carrier
    [NormedSpace ℝ X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {f : X → E} (hf : Continuous f) : Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact hK (μ := μ)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hμ] at h

lemma hasDerivAt_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x,F (t,x) ∂μ)
      (∫ x,fderiv ℝ F (t,x) (1,0) ∂μ) t := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (f := fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) hd.continuous.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (t-1) (t+1)) (bound := fun _ : X ↦ M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_of_continuous_compact_carrier hK hμ (hF.continuous.comp (continuous_const.prodMk continuous_id)))
    ((hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (hμ.mono fun x hx s hs ↦ hM (s,x) ⟨hs,hx⟩)
    (integrable_const M) ?_).2
  exact Eventually.of_forall fun x s _ ↦
    (hF.differentiable (by simp) (s,x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))

theorem contDiff_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ x,F (t,x) ∂μ) := by
  have hfinite : ∀ n : ℕ,∀ F : ℝ×X → E,ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ n (fun t ↦ ∫ x,F (t,x) ∂μ) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t ↦
        (hasDerivAt_compact_parameter_integral hK hμ hF t).continuousAt)
    | succ n ih =>
      intro F hF
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
        (hF.fderiv_right (by simp)).clm_apply contDiff_const
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hasDerivAt_compact_parameter_integral hK hμ hF t).differentiableAt,by simp,?_⟩
      have heq : deriv (fun t ↦ ∫ x,F (t,x) ∂μ)=(fun t ↦ ∫ x,fderiv ℝ F (t,x) (1,0) ∂μ) :=
        funext fun t ↦ (hasDerivAt_compact_parameter_integral hK hμ hF t).deriv
      rw [heq]
      exact ih _ hd
  exact contDiff_infty.mpr fun n ↦ hfinite n F hF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cubeIntersection_compact_carrier (E : Set Torus) :
    ∀ᵐ x ∂(volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)),x∈closedFundamentalCube := by
  have hh := ae_restrict_mem measurableSet_fundamentalCube (μ := (volume : Measure Cover))
  have hh' := ae_restrict_of_ae_restrict_of_subset (t := fundamentalCube)
    (s := fundamentalCube∩quotientMap ⁻¹' E) inter_subset_left hh
  exact hh'.mono fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩

lemma smooth_quotient_extension {f g : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h0 : g 0≠0) :
    ∃ q : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) q ∧ q =ᶠ[𝓝 0] (fun t ↦ f t/g t) := by
  let S : Set ℝ := {t | g t≠0}
  have hS : IsOpen S := isOpen_ne.preimage hg.continuous
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds h0)
  let η : ContDiffBump (0 : ℝ) := ⟨r/4,r/2,by positivity,by linarith⟩
  have hsupp : tsupport η⊆S := by
    rw [η.tsupport_eq]
    intro t ht
    exact hsub (show dist t 0 < r from lt_of_le_of_lt ht (by change r/2 < r; linarith))
  refine ⟨fun t ↦ η t*(f t/g t),?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t∈tsupport η
    · exact η.contDiff.contDiffAt.mul (hf.contDiffAt.div hg.contDiffAt (hsupp ht))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
      simp [hs]
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) η.rIn_pos] with t ht
    rw [η.one_of_mem_closedBall (Metric.ball_subset_closedBall ht),one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousMass_smooth (l : List Variation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainMass (simultaneousChain l t) E) :=
  contDiff_compact_parameter_integral isCompact_closedFundamentalCube
    (cubeIntersection_compact_carrier E) (simultaneousJacobian_smooth l)

lemma simultaneousFlux_smooth (l : List Variation) (b : Variation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainTransportedFlux (simultaneousChain l t) b E) := by
  exact contDiff_compact_parameter_integral isCompact_closedFundamentalCube (cubeIntersection_compact_carrier E)
    (F := fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2 *
      fderiv ℝ b.function (chainMove (simultaneousChain l p.1) p.2) (EuclideanSpace.single b.coordinate 1))
    ((simultaneousJacobian_smooth l).mul
    (((b.smooth.fderiv_right (by simp)).clm_apply contDiff_const).comp (simultaneousMove_smooth l)))

lemma chainCorrection_zero (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E) : chainCorrection l b E 0=0 := by
  simp [chainCorrection,simultaneousMass_zero l hE]

lemma chainCorrection_eventually_exact (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) ∧
      torusVolume (chainRegion (simultaneousChain l t++[(b,chainCorrection l b E t)]) E)=torusVolume E := by
  have hden : chainTransportedFlux (simultaneousChain l 0) b E≠0 := by simpa
  have hc : ContinuousAt (chainCorrection l b E) 0 :=
    (continuousAt_const.sub (simultaneousMass_smooth l E).continuous.continuousAt).div
      (simultaneousFlux_smooth l b E).continuous.continuousAt hden
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),|chainCorrection l b E t| *(b.bound : ℝ)<1 :=
    (hc.abs.mul_const _).eventually (eventually_lt_nhds (by simp [chainCorrection_zero l b hE]))
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),chainTransportedFlux (simultaneousChain l t) b E≠0 :=
    (simultaneousFlux_smooth l b E).continuous.continuousAt.eventually_ne hden
  filter_upwards [simultaneousChain_eventually_valid l,hsmall,hne] with t ht hbt hnt
  have hv : ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) :=
    ht.append (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hbt)
  refine ⟨hv,?_⟩
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.mp
  rw [show (torusVolume (chainRegion _ E)).toReal=torusVolume.real (chainRegion _ E) from rfl,
    volume_chainRegion hv hE,chainMass_append]
  unfold chainCorrection
  rw [div_mul_cancel₀ _ hnt]
  dsimp only [Measure.real]
  ring

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothNormalLength_smooth : ContDiff ℝ (⊤ : ℕ∞) smoothNormalLength := by
  apply ((contDiff_norm_sq ℝ).add (normSmoothingBump.contDiff.comp (contDiff_norm_sq ℝ))).sqrt
  intro v
  apply ne_of_gt
  by_cases hv : v=0
  · subst v
    simp only [Function.comp_apply,norm_zero,zero_pow (by decide : 2≠0),zero_add]
    rw [normSmoothingBump.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [normSmoothingBump]))]
    norm_num
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hv)) normSmoothingBump.nonneg

lemma smoothNormalLength_eq {v : Cover} (hv : 1/2≤‖v‖) : smoothNormalLength v=‖v‖ := by
  unfold smoothNormalLength
  rw [normSmoothingBump.zero_of_le_dist,add_zero,Real.sqrt_sq (norm_nonneg _)]
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg ‖v‖)]
  change (1/4 : ℝ)≤‖v‖^2
  nlinarith

lemma normalCarrier_compact : IsCompact normalCarrier :=
  isCompact_closedFundamentalCube.prod (isCompact_sphere 0 1)

lemma normalEmbedding_mem (z : NormalBundle) : normalEmbedding z∈normalCarrier := by
  exact ⟨z.1.property,by simpa [Metric.mem_sphere,dist_zero_right,normalEmbedding] using z.2.property⟩

lemma normalMap_ae_carrier (μ : FiniteMeasure NormalBundle) :
    ∀ᵐ p ∂Measure.map normalEmbedding (μ : Measure NormalBundle),p∈normalCarrier := by
  exact (ae_map_iff normalEmbedding_continuous.measurable.aemeasurable
    (show MeasurableSet normalCarrier from normalCarrier_compact.measurableSet)).2
    (Eventually.of_forall normalEmbedding_mem)

theorem normalArea_smoothAt {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) 0 := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ p,smoothNormalLength (C (t,p))
      ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) :=
    contDiff_compact_parameter_integral normalCarrier_compact (normalMap_ae_carrier μ)
      (smoothNormalLength_smooth.comp hC)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hsmall] with t ht
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
  · apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
  · exact ((smoothNormalLength_smooth.comp hC).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma second_derivative_nonneg_of_local_min {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) : 0≤deriv (deriv f) t := by
  by_contra hn
  have hn' : deriv (deriv f) t<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn' hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] (fun _ ↦ f t) := by
    filter_upwards [hmin,hmax] with s hs hs'
    exact le_antisymm hs' hs
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CorrectedChain
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

lemma correctedChainCofactor_smooth (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (correctedChain l b γ p.1) p.2.1 p.2.2) := by
  simp only [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
  exact (simultaneousCofactor_smooth l).add ((hγ.comp contDiff_fst).fun_smul
    ((wallVelocity_contDiff b).comp
      (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk
        (simultaneousCofactor_smooth l))))

lemma correctedChainArea_smoothAt (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (μ : FiniteMeasure NormalBundle) : ContDiffAt ℝ (⊤ : ℕ∞) (correctedChainArea l b γ μ) 0 := by
  apply normalArea_smoothAt (correctedChainCofactor_smooth l b hγ) ?_ μ
  intro p _
  simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]

lemma correctedChainArea_zero (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    correctedChainArea l b γ μ 0=(μ.mass : ℝ) := by
  unfold correctedChainArea
  simp_rw [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0,
    zero_smul,add_zero,simultaneousCofactor_zero,fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const,smul_eq_mul,mul_one]
  rfl

theorem isMinimizerAt_chain_stability {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (l : List Variation) (b : Variation)
    (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
        torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E) ∧
      IsLocalMin (correctedChainArea l b γ μ) 0 ∧
      0≤deriv (deriv (correctedChainArea l b γ μ)) 0 := by
  obtain ⟨γ,hγ,heq⟩ := smooth_quotient_extension
    (contDiff_const.sub (simultaneousMass_smooth l E)) (simultaneousFlux_smooth l b E)
    (by simpa using hB)
  have heq' : γ =ᶠ[𝓝 0] chainCorrection l b E := heq
  have hγ0 : γ 0=0 := heq'.eq_of_nhds.trans (chainCorrection_zero l b hE)
  have hvol : ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
      torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E := by
    filter_upwards [heq',chainCorrection_eventually_exact l b hE hB] with t ht hv
    simpa only [correctedChain,ht] using hv
  have hlocal : IsLocalMin (correctedChainArea l b γ μ) 0 := by
    filter_upwards [hvol] with t ht
    rw [correctedChainArea_zero l b hγ0,hμ.1]
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hleast := hmin.2.2 _ hfin (ht.2.trans hmin.2.1)
    have harea := perimeter_chainRegion_le_normalArea ht.1 hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _),correctedChainArea] using hh
  exact ⟨γ,hγ,hγ0,hvol,hlocal,second_derivative_nonneg_of_local_min hlocal
    (correctedChainArea_smoothAt l b hγ hγ0 μ).continuousAt⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma hasDerivAt_norm_curve {f : ℝ → X} {v : X} {t : ℝ}
    (hf : HasDerivAt f v t) (h0 : f t≠0) :
    HasDerivAt (fun s ↦ ‖f s‖) (⟪f t,v⟫/‖f t‖) t := by
  have hh := hf.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1 <;> first | rfl | ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] in
lemma deriv_parameter_slice
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E]
    {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : X) :
    deriv (fun s ↦ F (s,x)) t=fderiv ℝ F (t,x) (1,0) :=
  ((hF.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma deriv_smooth_add {f g : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : deriv (fun t ↦ f t+g t)=fun t ↦ deriv f t+deriv g t := by
  funext t
  exact ((hf.differentiable (by simp) t).hasDerivAt.add
    (hg.differentiable (by simp) t).hasDerivAt).deriv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalArea_first_derivative {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) 0 =
      ∫ z,⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫
        ∂(μ : Measure NormalBundle) := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  let F : ℝ×(Cover×Cover) → ℝ := fun p ↦ smoothNormalLength (C p)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := smoothNormalLength_smooth.comp hC
  have heq : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) =ᶠ[𝓝 0]
      (fun t ↦ ∫ p,F (t,p) ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    filter_upwards [hsmall] with t ht
    rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
    · apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [heq.deriv_eq,(hasDerivAt_compact_parameter_integral normalCarrier_compact
    (normalMap_ae_carrier μ) hF 0).deriv]
  have hm : AEStronglyMeasurable (fun p : Cover×Cover ↦ fderiv ℝ F (0,p) (1,0))
      (Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ F p (1,0)) :=
      (hF.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hz : (fun t ↦ F (t,normalEmbedding z)) =ᶠ[𝓝 0] (fun t ↦ ‖C (t,normalEmbedding z)‖) := by
    filter_upwards [hsmall] with t ht
    exact smoothNormalLength_eq (ht _ (normalEmbedding_mem z))
  dsimp only
  rw [← deriv_parameter_slice hF,hz.deriv_eq]
  have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
    hC.comp (contDiff_id.prodMk contDiff_const)
  have hc0 := h0 _ (normalEmbedding_mem z)
  have hn : C (0,normalEmbedding z)≠0 := by
    rw [hc0]
    exact norm_ne_zero_iff.mp (by rw [show ‖(normalEmbedding z).2‖=1 from z.2.property]; norm_num)
  rw [(hasDerivAt_norm_curve (hcz.differentiable (by simp) 0).hasDerivAt hn).deriv,hc0]
  simp only [normalEmbedding,z.2.property,div_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousMass_single (a : Variation) {E : Set Torus} (hE : MeasurableSet E) (t : ℝ) :
    chainMass (simultaneousChain [a] t) E=torusVolume.real E+t*directionalFlux E a.coordinate a.function := by
  have h := chainMass_append [] a t E
  simpa only [simultaneousChain,List.map_cons,List.map_nil,List.nil_append,chainMass,chainJacobian,chainTransportedFlux,chainMove,mul_one,one_mul,directionalFlux,
    setIntegral_one_eq_measureReal,← realVolume_lift hE] using h

lemma correctedSingleCofactor_deriv (a b : Variation) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (x n : Cover) :
    deriv (fun t ↦ chainCofactor (correctedChain [a] b γ t) x n) 0=
      coordinateNormalVelocity a.coordinate a.function x n+
        deriv γ 0 • coordinateNormalVelocity b.coordinate b.function x n := by
  let P : ℝ → Cover := fun t ↦ coordinateNormalVelocity b.coordinate b.function
    (coordinateMove a.coordinate a.function t x) (coordinateCofactor a.coordinate a.function t x n)
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) :=
    contDiff_const.add ((contDiff_id.mul contDiff_const).smul contDiff_const)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateCofactor a.coordinate a.function t x n) := by
    simp only [coordinateCofactor_eq]
    exact contDiff_const.add (contDiff_id.fun_smul contDiff_const)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp (hm.prodMk hc)
  have he : (fun t ↦ chainCofactor (correctedChain [a] b γ t) x n)=
      (fun t ↦ n+t • coordinateNormalVelocity a.coordinate a.function x n+γ t • P t) := by
    funext t
    simp only [correctedChain,simultaneousChain,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      chainCofactor,coordinateCofactor_eq,P]
  rw [he]
  have hd := ((hasDerivAt_const (0 : ℝ) n).fun_add
    ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateNormalVelocity a.coordinate a.function x n))).fun_add
      ((hγ.differentiable (by simp) 0).hasDerivAt.fun_smul (hP.differentiable (by simp) 0).hasDerivAt)
  simpa [hγ0,P,coordinateMove,coordinateCofactor_eq] using hd.deriv

lemma correctedSingleArea_deriv (a b : Variation) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (correctedChainArea [a] b γ μ) 0=normalFirstVariation μ a+
      deriv γ 0*normalFirstVariation μ b := by
  have h := normalArea_first_derivative (correctedChainCofactor_smooth [a] b hγ)
      (by intro p _; simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]) μ
  change deriv (correctedChainArea [a] b γ μ) 0 = _ at h
  rw [h]
  simp only [normalEmbedding,correctedSingleCofactor_deriv a b hγ hγ0,inner_add_right,real_inner_smul_right]
  rw [integral_add,integral_const_mul]
  · rfl
  · exact (continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity a.coordinate a.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity b.coordinate b.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

theorem isMinimizerAt_mixed_stationary {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a b : Variation) (hB : directionalFlux E b.coordinate b.function≠0) :
    normalFirstVariation μ a*directionalFlux E b.coordinate b.function=
      normalFirstVariation μ b*directionalFlux E a.coordinate a.function := by
  obtain ⟨γ,hγ,hγ0,hvol,hlocal,_⟩ := isMinimizerAt_chain_stability hmin hE hμ [a] b hB
  have hex : (fun t ↦ chainMass (simultaneousChain [a] t) E+
      γ t*chainTransportedFlux (simultaneousChain [a] t) b E) =ᶠ[𝓝 0]
      (fun _ ↦ torusVolume.real E) := by
    filter_upwards [hvol] with t ht
    rw [← chainMass_append]
    change chainMass (correctedChain [a] b γ t) E=torusVolume.real E
    rw [← volume_chainRegion ht.1 hE]
    exact congrArg ENNReal.toReal ht.2
  have hd := hex.deriv_eq
  have hm : (fun t ↦ chainMass (simultaneousChain [a] t) E)=
      (fun t ↦ torusVolume.real E+t*directionalFlux E a.coordinate a.function) :=
    funext (simultaneousMass_single a hE)
  have hm' : deriv (fun t ↦ chainMass (simultaneousChain [a] t) E) 0=
      directionalFlux E a.coordinate a.function := by rw [hm]; simp
  rw [deriv_smooth_add (simultaneousMass_smooth [a] E)
    (hγ.mul (simultaneousFlux_smooth [a] b E))] at hd
  dsimp only at hd
  rw [hm',(show deriv (fun t ↦ γ t*chainTransportedFlux (simultaneousChain [a] t) b E) 0=
      deriv γ 0*directionalFlux E b.coordinate b.function from by
        simpa [hγ0] using ((hγ.differentiable (by simp) 0).hasDerivAt.fun_mul
          ((simultaneousFlux_smooth [a] b E).differentiable (by simp) 0).hasDerivAt).deriv),deriv_const] at hd
  have ha := hlocal.deriv_eq_zero
  rw [correctedSingleArea_deriv a b hγ hγ0 μ] at ha
  nlinarith [congrArg (fun z ↦ z*directionalFlux E b.coordinate b.function) ha,
    congrArg (fun z ↦ z*normalFirstVariation μ b) hd]

 theorem isMinimizerAt_exists_coordinate_multiplier {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (b : Variation) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ H : ℝ,∀ a : Variation,normalFirstVariation μ a=H*directionalFlux E a.coordinate a.function := by
  refine ⟨normalFirstVariation μ b/directionalFlux E b.coordinate b.function,fun a ↦ ?_⟩
  apply mul_right_cancel₀ hB
  rw [isMinimizerAt_mixed_stationary hmin hE hμ a b hB]
  field_simp

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TubeCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology

namespace CubicTorus.Reduction

lemma second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  rw [hz] at hneg
  exact (lt_irrefl 0) hneg

end CubicTorus.Reduction

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TorusCoordinatePermute
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

lemma openRepresentative_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    openRepresentative E=openRepresentative F := by
  unfold openRepresentative
  apply congrArg (fun A : Set Torus ↦ Aᶜ)
  apply volumeSupport_congr_ae
  filter_upwards [h] with z hz
  exact congrArg Not hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

namespace Periodic

theorem isMinimizerAt_connected_strict_support {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (C : ℝ → ℝ),
      IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      deriv (deriv C) V<0 := by
  obtain ⟨μ,H,N,C,hμ,hN,hp,hae,hCMC,hs,hd,hdd⟩ :=
    isMinimizerAt_exact_profile_hessian hV hE hmin
  have hpos := isMinimizerAt_connected_curvature_integral_pos hV hE hmin hc hμ hN hp hae
  refine ⟨μ,H,C,hμ,hCMC,hs,hd,?_⟩
  have hprod : (isoperimetricProfile V)^2*deriv (deriv C) V<0 := by
    rw [hdd]; linarith
  by_contra! hnon
  exact (mul_nonneg (sq_nonneg _) hnon).not_gt hprod

theorem isMinimizerAt_profile_local_min_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hloc : IsLocalMin isoperimetricProfile V) :
    perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E := by
  apply (isMinimizerAt_connected_or_standard_slab hV hmin).resolve_left
  intro hc
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    rwa [openRepresentative_congr_ae hae]
  obtain ⟨μ,H,C,hμ,hCMC,hs,hd,hdd⟩ := isMinimizerAt_connected_strict_support hV hF hmF hcF
  have hmC : IsLocalMin C V := by
    filter_upwards [hloc,hs.above] with W hW hWa
    change C V≤C W
    rw [hs.contact]
    exact hW.trans hWa
  exact (Reduction.second_deriv_nonneg_of_local_min hmC hs.smooth.continuousAt).not_gt hdd

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_TorusCylinders
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusCoordinatePermute_measurePreserving (e : Fin 3 ≃ Fin 3) :
    MeasurePreserving (torusCoordinatePermute e) torusVolume torusVolume := by
  convert product_to_torus_measurePreserving.comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => AddCircle (1 : ℝ)) e.symm).comp
      torus_to_product_measurePreserving) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  ext i
  simp [Function.comp_def,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft]

lemma quotientMap_coordinatePermute (e : Fin 3 ≃ Fin 3) (x : Cover) :
    quotientMap (coverCoordinatePermute e x)=torusCoordinatePermute e (quotientMap x) := rfl

lemma coverCoordinatePermute_lattice (e : Fin 3 ≃ Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinatePermute e (latticeVector m)=latticeVector (fun j => m (e j)) := rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinatePermutedField_contDiff (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinatePermutedField e F) :=
  (coverCoordinatePermute e.symm).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinatePermute e).toContinuousLinearEquiv.contDiff)

lemma coordinatePermutedField_periodic (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinatePermutedField e F (x+latticeVector n)=coordinatePermutedField e F x := by
  intro n x
  simp only [coordinatePermutedField,map_add,coverCoordinatePermute_lattice,hp]

lemma coordinatePermutedField_admissible (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinatePermutedField e F) := by
  refine ⟨coordinatePermutedField_contDiff e hF.1,coordinatePermutedField_periodic e hF.2.1,?_⟩
  intro x
  simpa only [coordinatePermutedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinatePermute e x)

lemma coordinatePermutedField_divergence (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinatePermutedField e F) x=divergence F (coverCoordinatePermute e x) := by
  have hd : HasFDerivAt (coordinatePermutedField e F)
      ((coverCoordinatePermute e.symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinatePermute e x)).comp
          (coverCoordinatePermute e).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinatePermute e.symm).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinatePermute e).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinatePermute_single,
    coverCoordinatePermute_apply]
  exact e.symm.sum_comp (fun j : Fin 3 => (fderiv ℝ F (coverCoordinatePermute e x) (EuclideanSpace.single j 1)) j)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinatePermute (e : Fin 3 ≃ Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (torusCoordinatePermute e ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinatePermutedField e.symm F) x := by
  have hm := (torusCoordinatePermute e).continuous.measurable
  have hr := coordinatePermutedField_admissible e.symm hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinatePermutedField e.symm F) (representative (torusCoordinatePermute e z))) := by
    funext z
    rw [coordinatePermutedField_divergence e.symm hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinatePermute e.symm (representative (torusCoordinatePermute e z))),
      quotientMap_coordinatePermute,quotientMap_representative]
    have hh : torusCoordinatePermute e.symm (torusCoordinatePermute e z)=z := by
      simpa only [Equiv.symm_symm] using torusCoordinatePermute_inverse e.symm z
    rw [hh]
  rw [he]
  exact (torusCoordinatePermute_measurePreserving e).setIntegral_preimage_emb
    (torusCoordinatePermute e).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinatePermutedField e.symm F) (representative z)) E

lemma perimeter_coordinatePermute_le (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinatePermute e hF hE]
  exact le_iSup_of_le (coordinatePermutedField e.symm F)
    (le_iSup_of_le (coordinatePermutedField_admissible e.symm hF) le_rfl)

lemma perimeter_coordinatePermute_measurable (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinatePermute_le e hE)
  have hh := perimeter_coordinatePermute_le e.symm ((torusCoordinatePermute e).continuous.measurable hE)
  have he : torusCoordinatePermute e.symm ⁻¹' (torusCoordinatePermute e ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

theorem perimeter_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp,← perimeter_congr_ae he]
  exact perimeter_coordinatePermute_measurable e (measurableSet_toMeasurable _ _)

lemma volume_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    torusVolume (torusCoordinatePermute e ⁻¹' E)=torusVolume E :=
  (torusCoordinatePermute_measurePreserving e).measure_preimage hE

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ChamberPositionProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_coordinate_multiplier {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ H : ℝ,∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function := by
  obtain ⟨i,f,hf,hp,hflux⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hm.1.1 hm.2.1)
  obtain ⟨D,hi,hfD⟩ := Periodic.exists_variation_of_function i hf hp
  have hD : directionalFlux E D.coordinate D.function≠0 := by
    rw [hi,hfD]; exact hflux.ne'
  exact Periodic.isMinimizerAt_exists_coordinate_multiplier hm hE hμ D hD

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalMeasureCoordinatePermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_permuteNormal (e : Fin 3 ≃ Fin 3) : Measurable (permuteNormal e) := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp ((torusCoordinatePermute e).continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact ((coverCoordinatePermute e).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma permuteNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (e : Fin 3 ≃ Fin 3) (z : NormalBundle) :
    F (permuteNormal e z).1=F (coverCoordinatePermute e z.1) := by
  change F (representative (torusCoordinatePermute e (quotientMap z.1)))=_
  rw [← quotientMap_coordinatePermute]
  exact periodic_representative hp _

lemma permuteNormal_mass (μ : FiniteMeasure NormalBundle) (e : Fin 3 ≃ Fin 3) :
    ((μ.map (permuteNormal e)).mass : ℝ)=(μ.mass : ℝ) := by
  have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_permuteNormal e)
    MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
  simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
    FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh

lemma coverCoordinatePermute_inner (e : Fin 3 ≃ Fin 3) (x y : Cover) :
    ⟪coverCoordinatePermute e x,y⟫=⟪x,coverCoordinatePermute e.symm y⟫ := by
  rw [← (coverCoordinatePermute e).inner_map_map x (coverCoordinatePermute e.symm y),
    coverCoordinatePermute_inverse]

theorem isNormalMeasure_coordinatePermute {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (e : Fin 3 ≃ Fin 3) :
    IsNormalMeasure (torusCoordinatePermute e ⁻¹' E) (μ.map (permuteNormal e.symm)) := by
  constructor
  · rw [permuteNormal_mass,hμ.1,perimeter_coordinatePermute_measurable e hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (permuteNormal e.symm) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_permuteNormal e.symm).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_coordinatePermute e hF hE,← hμ.2 _ (coordinatePermutedField_admissible e.symm hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change ⟪coverCoordinatePermute e.symm z.2,F (permuteNormal e.symm z).1⟫=
        ⟪(z.2 : Cover),coverCoordinatePermute e (F (coverCoordinatePermute e.symm z.1))⟫
      rw [permuteNormal_periodic_eval hF.2.1,coverCoordinatePermute_inner,Equiv.symm_symm]

lemma permuted_normal_ae {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (e : Fin 3 ≃ Fin 3) :
    ∀ᵐ z ∂(μ.map (permuteNormal e.symm) : Measure NormalBundle),
      coordinatePermutedField e N z.1=(z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map (permuteNormal e.symm) (μ : Measure NormalBundle),_
  apply (ae_map_iff (measurable_permuteNormal e.symm).aemeasurable
    (measurableSet_eq_fun
      (((coverCoordinatePermute e.symm).continuous.comp (hN.comp (coverCoordinatePermute e).continuous)).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [ha] with z hz
  change coordinatePermutedField e N (permuteNormal e.symm z).1=((permuteNormal e.symm z).2 : Cover)
  rw [permuteNormal_periodic_eval (coordinatePermutedField_periodic e hp)]
  change coverCoordinatePermute e.symm (N (coverCoordinatePermute e (coverCoordinatePermute e.symm z.1)))=_
  rw [coverCoordinatePermute_inverse,hz]
  rfl

lemma axialFluxWeight_permute (μ : FiniteMeasure NormalBundle) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    axialFluxWeight (μ.map (permuteNormal e)) i=axialFluxWeight μ (e i) := by
  unfold axialFluxWeight
  rw [permuteNormal_mass]
  congr 1
  change (∫ z,1-((z.2 : Cover) i)^2 ∂Measure.map (permuteNormal e) (μ : Measure NormalBundle))=_
  rw [integral_map (measurable_permuteNormal e).aemeasurable]
  · rfl
  · exact (continuous_const.sub (((EuclideanSpace.proj i).continuous.comp
      (continuous_subtype_val.comp continuous_snd)).pow 2)).aestronglyMeasurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finitePerimeter_coordinatePermute {E : Set Torus} (hE : FinitePerimeter E)
    (e : Fin 3 ≃ Fin 3) : FinitePerimeter (torusCoordinatePermute e ⁻¹' E) := by
  refine ⟨hE.1.preimage (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving,?_⟩
  rw [perimeter_coordinatePermute e hE.1]
  exact hE.2

theorem isMinimizerAt_coordinatePermute {E : Set Torus} {V : ℝ}
    (hE : IsMinimizerAt V E) (e : Fin 3 ≃ Fin 3) :
    IsMinimizerAt V (torusCoordinatePermute e ⁻¹' E) := by
  refine ⟨finitePerimeter_coordinatePermute hE.1 e,?_,?_⟩
  · rw [volume_coordinatePermute e hE.1.1,hE.2.1]
  · intro F hF hvF
    rw [perimeter_coordinatePermute e hE.1.1]
    exact hE.2.2 F hF hvF

lemma volumeSupport_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    volumeSupport (torusCoordinatePermute e ⁻¹' E)=torusCoordinatePermute e ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (torusCoordinatePermute e ⁻¹' E)∩Metric.ball a r=
      torusCoordinatePermute e ⁻¹' (E∩Metric.ball (torusCoordinatePermute e a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,(torusCoordinatePermute e).isometry.dist_eq]
  rw [he,Measure.real_def,Measure.real_def,
    (torusCoordinatePermute_measurePreserving e).measure_preimage
      (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    openRepresentative (torusCoordinatePermute e ⁻¹' E)=torusCoordinatePermute e ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_coordinatePermute hE.compl]
  rfl

lemma frontier_openRepresentative_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    frontier (openRepresentative (torusCoordinatePermute e ⁻¹' E))=
      torusCoordinatePermute e ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_coordinatePermute hE e]
  exact (torusCoordinatePermute e).toHomeomorph.preimage_frontier _ |>.symm

lemma coordinateReflection_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (z : Torus) :
    torusCoordinatePermute e (coordinateReflection i z)=
      coordinateReflection (e.symm i) (torusCoordinatePermute e z) := by
  ext j
  simp only [torusCoordinatePermute_apply,coordinateReflection_apply]
  simp only [show (j=e.symm i)↔e j=i from Equiv.eq_symm_apply e]

lemma reflection_invariant_coordinatePermute {E : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) (e : Fin 3 ≃ Fin 3) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' (torusCoordinatePermute e ⁻¹' E) =ᵐ[torusVolume]
      (torusCoordinatePermute e ⁻¹' E) := by
  intro i
  have hh := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq (hs (e.symm i))
  have he : coordinateReflection i ⁻¹' (torusCoordinatePermute e ⁻¹' E)=
      torusCoordinatePermute e ⁻¹' (coordinateReflection (e.symm i) ⁻¹' E) := by
    ext z
    simp only [mem_preimage,coordinateReflection_coordinatePermute]
  rwa [he]

lemma coordinateHalf_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (a : ℝ) (z : Torus) :
    torusCoordinatePermute e z∈coordinateHalf i a ↔ z∈coordinateHalf (e i) a := by
  rfl

lemma chamberVertex_coordinatePermute (e : Fin 3 ≃ Fin 3) (c b : Fin 3 → Bool) :
    coverCoordinatePermute e (chamberVertex (c ∘ e.symm) b)=chamberVertex c (b ∘ e) := by
  ext i
  simp [chamberVertex,chamberCorner]

lemma chamberSign_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) {N : Cover → Cover}
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (e : Fin 3 ≃ Fin 3) :
    ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative (torusCoordinatePermute e ⁻¹' E))∩
        coordinateHalf i (if (c ∘ e.symm) i then 0 else 1/2) →0 < coordinatePermutedField e N x i := by
  intro x i hx
  apply hsg (coverCoordinatePermute e x) (e.symm i)
  constructor
  · rw [quotientMap_coordinatePermute]
    change quotientMap x∈torusCoordinatePermute e ⁻¹' frontier (openRepresentative E)
    rw [← frontier_openRepresentative_coordinatePermute hE e]
    exact hx.1
  · rw [quotientMap_coordinatePermute,coordinateHalf_coordinatePermute,Equiv.apply_symm_apply]
    exact hx.2

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_MinimizerFirstTransitionTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fin3_pair_complement (i j : Fin 3) (hij : i≠j) :
    ∃ k : Fin 3,(fun x : Fin 3 => decide (x=i ∨ x=j))=(fun x => decide (x≠k)) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact ⟨0,by decide⟩ | exact ⟨1,by decide⟩ | exact ⟨2,by decide⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FourStarScalarGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma secondTransition_mem_Ioo_half : 1/Real.pi∈Ioo (0 : ℝ) (1/2) := by
  exact ⟨by positivity,(div_lt_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_second_transition_corner_excluded
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (1/Real.pi) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (hw0 : 2/3≤axialFluxWeight μ 0) (hw1 : axialFluxWeight μ 0<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : False := by
  have hvh := secondTransition_mem_Ioo_half
  have hV : 1/Real.pi∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier hV hE hm hμ
  obtain ⟨hA,_,hA1,hh,hr,hrV,_,hs1,hb,_,htop,hbottom,hdrop⟩ :=
    isMinimizerAt_four_corner_necessary_data hvh hE hm hμ hN hp ha hs hsg hH ht1 ht2 hb1 hb2
  exact secondCorner_endpoint_contradiction hA hA1 hh hb hw1 hr hrV hs1 htop hbottom hdrop hw0
    (isMinimizerAt_second_endpoint_linear_bound hE hm hμ hH).le

theorem isMinimizerAt_second_transition_standard {E : Set Torus}
    (hmE : IsMinimizerAt (1/Real.pi) E) : SmallStandardRegion (1/Real.pi) E := by
  by_contra hnstd
  obtain ⟨F,μ,N,hN,hp,c,H,hF,hm,hμ,ha,hs,hsg,hH,hws,hw,haxis,hface⟩ :=
    isMinimizerAt_second_transition_nonstandard_star hmE hnstd
  obtain ⟨i,hi⟩ : ∃ i : Fin 3,2/3≤axialFluxWeight μ i := by
    by_contra! hn
    rw [Fin.sum_univ_three] at hws
    linarith [hn 0,hn 1,hn 2]
  classical
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have he0 : e.symm 0=i := by simp [e]
  have he1 : e.symm 1≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have he2 : e.symm 2≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have hpair (j : Fin 3) : ((fun k : Fin 3 => decide (k=0 ∨ k=j)) ∘ e)=
      (fun k => decide (k=i ∨ k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply,he0]
  have hsingle (j : Fin 3) : ((fun k : Fin 3 => decide (k=j)) ∘ e)=
      (fun k => decide (k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply]
  have ht (j : Fin 3) (hj : j≠i) :
      quotientMap (chamberVertex c (fun k => decide (k=i ∨ k=j)))∉openRepresentative F := by
    obtain ⟨k,hk⟩ := fin3_pair_complement i j hj.symm
    rw [hk]
    exact fun h => hface k (subset_closure h)
  have hv (b : Fin 3 → Bool) :
      quotientMap (chamberVertex (c ∘ e.symm) b)∈openRepresentative (torusCoordinatePermute e ⁻¹' F) ↔
      quotientMap (chamberVertex c (b ∘ e))∈openRepresentative F := by
    rw [openRepresentative_coordinatePermute hF e]
    change torusCoordinatePermute e (quotientMap (chamberVertex (c ∘ e.symm) b))∈openRepresentative F ↔ _
    rw [← quotientMap_coordinatePermute,chamberVertex_coordinatePermute]
  apply isMinimizerAt_second_transition_corner_excluded
    ((torusCoordinatePermute e).continuous.measurable hF) (isMinimizerAt_coordinatePermute hm e)
    (isNormalMeasure_coordinatePermute hF hμ e)
    (coordinatePermutedField_contDiff e hN) (coordinatePermutedField_periodic e hp)
    (permuted_normal_ae hN.continuous hp ha e) (reflection_invariant_coordinatePermute hs e)
    (chamberSign_coordinatePermute hF hsg e)
  · simpa [axialFluxWeight_permute,e] using hi
  · rw [axialFluxWeight_permute]
    exact (hw _).2
  · rw [hv,hpair]
    exact ht _ he1
  · rw [hv,hpair]
    exact ht _ he2
  · rw [hv,hsingle]
    exact haxis _
  · rw [hv,hsingle]
    exact haxis _
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_small_slab_standard_oai {V : ℝ} (hV : V∈Icc TwoVolume.V₂ (1/2))
    {E : Set Torus} (hm : IsMinimizerAt V E) : SmallStandardRegion V E := by
  rcases eq_or_lt_of_le hV.1 with he|he
  · subst V
    exact isMinimizerAt_second_transition_standard hm
  have hv2 := secondTransition_mem_Ioo_half
  have hv : V∈Ioo (0 : ℝ) 1 := ⟨hv2.1.trans_le hV.1,by linarith [hV.2]⟩
  have hc := isoperimetricProfile_slab_local_min (show V∈Ioo TwoVolume.V₂ (1-TwoVolume.V₂) from
    ⟨he,by change V<1-1/Real.pi; linarith [hV.2,hv2.2]⟩)
  have hh := Periodic.isMinimizerAt_profile_local_min_slab hv hm hc
  simpa only [StandardRegionAt,ite_eq_left hV.2] using hh.2.2

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_small_slab_standard_oai := @OAI.CubicTorus.isMinimizerAt_small_slab_standard_oai
