-- Prove2me | solution 1 for OAI.CubicTorus.profile_upper_support_power_secant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:41:49.085355+00:00
-- url     : https://prove2.me/submissions/75cd92fd-402a-44e7-b195-863dd4e0156c

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_continuousOn_isoperimetricProfile
import Theorems.Thm_OAI_CubicTorus_isoperimetricProfile_power_upper_support

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

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

lemma lift_indicator_integral {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (g : Cover → ℝ) :
    (∫ x in fundamentalCube, (quotientMap ⁻¹' E).indicator g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  rw [integral_indicator₀ hm, Measure.restrict_restrict₀ hm, inter_comm]

lemma characteristic_mul (E : Set Torus) (g : Cover → ℝ) (x : Cover) :
    characteristic E (quotientMap x) * g x = (quotientMap ⁻¹' E).indicator g x := by
  classical
  by_cases hx : quotientMap x ∈ E <;> simp [characteristic, hx]

theorem tendsto_lift_integral {Es : ℕ → Set Torus} {E : Set Torus}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    {g : Cover → ℝ} (hg : IntegrableOn g fundamentalCube) :
    Filter.Tendsto
      (fun n => ∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, g x)
      Filter.atTop (nhds (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x)) := by
  have hms (n : ℕ) := (hEs n).preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hlift := ae_of_ae_map measurable_quotientMap.aemeasurable hlim
  have hconv : ∀ᵐ x ∂volume.restrict fundamentalCube,
      Filter.Tendsto (fun n => (quotientMap ⁻¹' Es n).indicator g x)
        Filter.atTop (nhds ((quotientMap ⁻¹' E).indicator g x)) := by
    filter_upwards [hlift] with x hx
    simpa only [characteristic_mul] using hx.mul_const (g x)
  have hdom := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (hg.indicator₀ (hms n)).aestronglyMeasurable) hg.norm
    (fun n => Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _)) hconv
  simpa only [lift_indicator_integral hE, lift_indicator_integral (hEs _)] using hdom

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

theorem tendsto_volume_of_ae_tendsto {Es : ℕ → Set Torus} {E : Set Torus}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x))) :
    Filter.Tendsto (fun n => torusVolume (Es n)) Filter.atTop (nhds (torusVolume E)) := by
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Torus => (1 : ℝ))
    (fun n => ((integrable_const (1 : ℝ)).indicator₀ (hEs n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => Filter.Eventually.of_forall (fun x => by
      change ‖(Es n).indicator (fun _ => (1 : ℝ)) x‖ ≤ 1
      simpa only [norm_one] using norm_indicator_le_norm_self (s := Es n) (fun _ => (1 : ℝ)) x))
    hlim
  change Filter.Tendsto (fun n => ∫ x, characteristic (Es n) x ∂torusVolume)
    Filter.atTop (nhds (∫ x, characteristic E x ∂torusVolume)) at hconv
  simp only [integral_characteristic (hEs _), integral_characteristic hE] at hconv
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

theorem perimeter_le_of_ae_tendsto_bound {Es : ℕ → Set Torus} {E : Set Torus}
    {Ls : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    (hbound : ∀ n, perimeter (Es n) ≤ Ls n)
    (hL : Filter.Tendsto Ls Filter.atTop (nhds L)) : perimeter E ≤ L := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_lift_integral hEs hE hlim (integrableOn_divergence hF.1))
  apply le_of_tendsto_of_tendsto ht hL
  apply Filter.Eventually.of_forall
  intro n
  exact (le_iSup₂ (f := fun F (_ : AdmissibleField F) =>
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, divergence F x)) F hF).trans (hbound n)

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

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

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
open scoped Topology Convolution

lemma smoothApprox_lipschitz {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) : LipschitzWith (smoothApproxLip n) (smoothApprox g n) := by
  have hφ := (mollifier n).contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))
  have hφc := (mollifier n).hasCompactSupport_normed (μ := volume)
  have hd (x) := hφc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))
    (locallyIntegrable_of_bounded hg hb) x
  have hdi : Integrable (fun y : Cover => ‖fderiv ℝ ((mollifier n).normed volume) y‖)
      volume :=
    (hφ.continuous_fderiv (by simp)).norm.integrable_of_hasCompactSupport (hφc.fderiv ℝ).norm
  apply lipschitzWith_of_nnnorm_fderiv_le ((smoothApprox_contDiff hg hb n).differentiable (by simp))
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (smoothApprox g n) x‖ ≤ _
  change ‖fderiv ℝ (((mollifier n).normed volume) ⋆ g) x‖ ≤ _
  rw [(hd x).fderiv, convolution_def]
  apply norm_integral_le_of_norm_le hdi
  exact Eventually.of_forall fun y => by
    have heq : ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Cover
        (fderiv ℝ ((mollifier n).normed volume) y)) (g (x - y)) =
        g (x - y) • fderiv ℝ ((mollifier n).normed volume) y := by
      ext v
      simp [ContinuousLinearMap.precompL_apply, mul_comm]
    rw [heq, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb (x - y))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

lemma torusApprox_sub_eq_integral {E : Set Torus} (hE : MeasurableSet E) (n : ℕ) (x : Torus) :
    torusApprox E n x - characteristic E x =
      ∫ y : Cover, (mollifier n).normed volume y *
        (characteristic E (x - quotientMap y) - characteristic E x) := by
  have hm : Measurable (fun y => characteristic E (x - quotientMap y)) :=
    (measurable_characteristic hE).comp (measurable_const.sub measurable_quotientMap)
  have hi := ((mollifier n).integrable_normed (μ := volume)).mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun y => characteristic_bound E (x - quotientMap y))
  simp_rw [mul_sub]
  rw [integral_sub hi ((mollifier n).integrable_normed.mul_const _),
    integral_mul_const, (mollifier n).integral_normed, one_mul]
  congr 1
  simp only [torusApprox, smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, Function.comp_def, quotientMap_sub, quotientMap_representative]

theorem torusApprox_error {E : Set Torus} (hE : MeasurableSet E) (hP : perimeter E ≠ ⊤)
    (n : ℕ) :
    (∫ x, |torusApprox E n x - characteristic E x| ∂torusVolume) ≤
      (mollifier n).rOut * (perimeter E).toReal := by
  let φ : Cover → ℝ := (mollifier n).normed volume
  let d : Torus × Cover → ℝ := fun z =>
    |characteristic E (z.1 - quotientMap z.2) - characteristic E z.1|
  have hφ : Integrable φ volume := (mollifier n).integrable_normed
  have hφm : Measurable φ := ((mollifier n).contDiff_normed (n := (⊤ : ℕ∞))).continuous.measurable
  have hd : Measurable d := by
    exact (((measurable_characteristic hE).comp
      (measurable_fst.sub (measurable_quotientMap.comp measurable_snd))).sub
        ((measurable_characteristic hE).comp measurable_fst)).abs
  have hd_bound (z) : |d z| ≤ 1 := by
    rcases characteristic_dichotomy E (z.1 - quotientMap z.2) with h | h <;>
      rcases characteristic_dichotomy E z.1 with h' | h' <;> simp [d, h, h']
  have hbase : Integrable (fun z : Torus × Cover => φ z.2) (torusVolume.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := torusVolume)).mul_prod hφ
  have hprod : Integrable (fun z : Torus × Cover => φ z.2 * d z) (torusVolume.prod volume) :=
    hbase.mul_bdd hd.aestronglyMeasurable (Eventually.of_forall hd_bound)
  have hip (x : Torus) : Integrable
      (fun y : Cover => φ y * (characteristic E (x - quotientMap y) - characteristic E x)) volume := by
    apply hφ.mul_bdd (c := 1)
      (((measurable_characteristic hE).comp (measurable_const.sub measurable_quotientMap)).sub
        measurable_const).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rcases characteristic_dichotomy E (x - quotientMap y) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
  have hinside (x : Torus) : |torusApprox E n x - characteristic E x| ≤
      ∫ y : Cover, φ y * d (x, y) := by
    rw [torusApprox_sub_eq_integral hE]
    calc
      _ ≤ ∫ y : Cover, ‖φ y * (characteristic E (x - quotientMap y) - characteristic E x)‖ :=
        norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp [d, Real.norm_eq_abs, abs_of_nonneg ((mollifier n).nonneg_normed y), φ]
  have hipx (y : Cover) : Integrable (fun x : Torus => d (x, y)) torusVolume := by
    apply Integrable.of_bound (hd.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => hd_bound (x, y)
  have htrans (y : Cover) : (∫ x, d (x, y) ∂torusVolume) ≤ ‖y‖ * (perimeter E).toReal :=
    characteristic_translation_bound hE hP y
  have hkernel (y : Cover) : φ y * (∫ x, d (x, y) ∂torusVolume) ≤
      φ y * ((mollifier n).rOut * (perimeter E).toReal) := by
    by_cases hy : φ y = 0
    · simp [hy]
    have hy' : y ∈ Metric.ball (0 : Cover) (mollifier n).rOut := by
      rw [← (mollifier n).support_normed_eq (μ := (volume : Measure Cover))]
      exact hy
    have hnorm : ‖y‖ ≤ (mollifier n).rOut := le_of_lt (by simpa using hy')
    exact mul_le_mul_of_nonneg_left
      ((htrans y).trans (mul_le_mul_of_nonneg_right hnorm ENNReal.toReal_nonneg))
        ((mollifier n).nonneg_normed y)
  calc
    _ ≤ ∫ x, ∫ y : Cover, φ y * d (x, y) ∂volume ∂torusVolume := by
      exact integral_mono ((torusApprox_integrable hE n).sub (integrable_characteristic hE)).abs
        hprod.integral_prod_left hinside
    _ = ∫ y : Cover, ∫ x, φ y * d (x, y) ∂torusVolume := integral_integral_swap hprod
    _ = ∫ y : Cover, φ y * (∫ x, d (x, y) ∂torusVolume) := by
      simp_rw [integral_const_mul]
    _ ≤ ∫ y : Cover, φ y * ((mollifier n).rOut * (perimeter E).toReal) := by
      apply integral_mono _ (hφ.mul_const _) hkernel
      simpa only [integral_const_mul] using hprod.integral_prod_right
    _ = _ := by rw [integral_mul_const, (mollifier n).integral_normed, one_mul]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma cubeToL1_lipschitz : LipschitzWith 1 cubeToL1 := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [NNReal.coe_one, one_mul]
  have hi : Integrable (fun x => dist (f (cubeRepresentative x)) (g (cubeRepresentative x)))
      torusVolume := by
    simpa only [dist_eq_norm, Pi.sub_apply] using ((integrable_cubeEval f).sub (integrable_cubeEval g)).norm
  calc
    _ = ∫ x, dist (f (cubeRepresentative x)) (g (cubeRepresentative x)) ∂torusVolume := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [(integrable_cubeEval f).coeFn_toL1, (integrable_cubeEval g).coeFn_toL1] with x hx hx'
      change dist ((integrable_cubeEval f).toL1 _ x) ((integrable_cubeEval g).toL1 _ x) = _
      rw [hx, hx']
    _ ≤ ∫ _x : Torus, dist f g ∂torusVolume :=
      integral_mono hi (integrable_const _) (fun x => BoundedContinuousFunction.dist_coe_le_dist _)
    _ = _ := by simp

lemma dist_torusApproxL1 {E : Set Torus} (hE : MeasurableSet E) (hP : perimeter E ≠ ⊤) (n : ℕ) :
    dist (characteristicL1 E hE) (torusApproxL1 E hE n) ≤
      (mollifier n).rOut * (perimeter E).toReal := by
  calc
    _ = ∫ x, |torusApprox E n x - characteristic E x| ∂torusVolume := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [(integrable_characteristic hE).coeFn_toL1,
        (torusApprox_integrable hE n).coeFn_toL1] with x hx hx'
      change dist ((integrable_characteristic hE).toL1 _ x) ((torusApprox_integrable hE n).toL1 _ x) = _
      rw [hx, hx', Real.dist_eq, abs_sub_comm]
    _ ≤ _ := torusApprox_error hE hP n

lemma totallyBounded_torusApproxL1 {ι : Type*} (Es : ι → Set Torus)
    (hEs : ∀ i, MeasurableSet (Es i)) (n : ℕ) :
    TotallyBounded (range (fun i => torusApproxL1 (Es i) (hEs i) n)) := by
  let F : ι → BoundedContinuousFunction CompactCell ℝ := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => smoothApprox (characteristic (Es i) ∘ quotientMap) n x,
      (smoothApprox_contDiff ((measurable_characteristic (hEs i)).comp measurable_quotientMap)
        (fun x => characteristic_bound (Es i) (quotientMap x)) n).continuous.comp continuous_subtype_val⟩
  have hLip (i) : LipschitzWith (smoothApproxLip n) (F i) := by
    change LipschitzWith (smoothApproxLip n)
      (smoothApprox (characteristic (Es i) ∘ quotientMap) n ∘ (Subtype.val : CompactCell → Cover))
    simpa only [mul_one] using
      (smoothApprox_lipschitz ((measurable_characteristic (hEs i)).comp measurable_quotientMap)
        (fun x => characteristic_bound (Es i) (quotientMap x)) n).comp
          (LipschitzWith.subtype_val closedFundamentalCube)
  have hEq : Equicontinuous ((↑) : range F → CompactCell → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (smoothApproxLip n)
    rintro ⟨_, i, rfl⟩
    exact hLip i
  have hbounded (f : BoundedContinuousFunction CompactCell ℝ) (x : CompactCell) (hf : f ∈ range F) : f x ∈ Icc (-1) 1 := by
    obtain ⟨i, rfl⟩ := hf
    exact abs_le.mp (smoothApprox_bound (fun y => characteristic_bound (Es i) (quotientMap y)) n x)
  have hcompact := BoundedContinuousFunction.arzela_ascoli (Icc (-1 : ℝ) 1) isCompact_Icc
    (range F) hbounded hEq
  apply ((hcompact.image cubeToL1_lipschitz.continuous).totallyBounded).subset
  rintro _ ⟨i, rfl⟩
  exact ⟨F i, subset_closure (mem_range_self i), rfl⟩

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma totallyBounded_characteristicL1 {ι : Type*} (Es : ι → Set Torus)
    (hEs : ∀ i, MeasurableSet (Es i)) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, perimeter (Es i) ≤ ENNReal.ofReal C) :
    TotallyBounded (range (fun i => characteristicL1 (Es i) (hEs i))) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hconv : Tendsto (fun n => (mollifier n).rOut * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using mollifier_rOut_tendsto.mul_const C
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (totallyBounded_torusApproxL1 Es hEs n) (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy, hiy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨y, hy, ?_⟩
  change dist (characteristicL1 (Es i) (hEs i)) y < ε
  have hfin : perimeter (Es i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hP i)
  have hreal : (perimeter (Es i)).toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top (hP i)
  have hdist : dist (characteristicL1 (Es i) (hEs i)) (torusApproxL1 (Es i) (hEs i) n) < ε / 2 :=
    ((dist_torusApproxL1 (hEs i) hfin n).trans
      (mul_le_mul_of_nonneg_left hreal (mollifier n).rOut_pos.le)).trans_lt hn
  have hiy' : dist (torusApproxL1 (Es i) (hEs i) n) y < ε / 2 := hiy
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem exists_ae_tendsto_characteristic {Es : ℕ → Set Torus}
    (hEs : ∀ n, MeasurableSet (Es n)) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ n, perimeter (Es n) ≤ ENNReal.ofReal C) :
    ∃ E : Set Torus, MeasurableSet E ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂torusVolume, Tendsto (fun n => characteristic (Es (ns n)) x) atTop
        (𝓝 (characteristic E x)) := by
  let fs : ℕ → Lp ℝ 1 torusVolume := fun n => characteristicL1 (Es n) (hEs n)
  have hcompact : IsCompact (closure (range fs)) :=
    (totallyBounded_characteristicL1 Es hEs hC hP).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨f, _, ns, hns, hconv⟩ := hcompact.isSeqCompact.subseq_of_frequently_in
    (Frequently.of_forall (fun n => subset_closure (mem_range_self n)))
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂torusVolume, ∀ n, (fs (ns (ms n))) x = characteristic (Es (ns (ms n))) x :=
    ae_all_iff.mpr (fun n => (integrable_characteristic (hEs (ns (ms n)))).coeFn_toL1)
  let E : Set Torus := {x | f x = 1}
  have hE : MeasurableSet E := (Lp.stronglyMeasurable f).measurable (measurableSet_singleton 1)
  refine ⟨E, hE, ns ∘ ms, hns.comp hms, ?_⟩
  filter_upwards [hae, hcoe] with x hx hcx
  have ht : Tendsto (fun n => characteristic (Es (ns (ms n))) x) atTop (𝓝 (f x)) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact (hcx n).symm
  have hfx : f x ∈ ({0, 1} : Set ℝ) := by
    apply ((finite_singleton (1 : ℝ)).insert 0).isClosed.mem_of_tendsto ht
    exact Eventually.of_forall fun n => by
      rcases characteristic_dichotomy (Es (ns (ms n))) x with h | h <;> simp [h]
  have hchar : characteristic E x = f x := by
    rcases mem_insert_iff.mp hfx with hzero | hone
    · have hxE : x ∉ E := by simp only [E, mem_ofPred_eq, hzero]; norm_num
      simp [characteristic, hxE, hzero]
    · have hxE : x ∈ E := hone
      simpa [characteristic, hxE] using hone.symm
  simpa only [Function.comp_apply, hchar] using ht

end CubicTorus

namespace CubicTorus

lemma measurableSet_stripe (V : ℝ) : MeasurableSet (stripe V) := by
  apply measurableSet_lt _ measurable_const
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))

lemma stripe_lift_preimage {V : ℝ} (hV : V ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' stripe V) =
      univ.pi (fun i : Fin 3 => Ico 0 (stripeUpper V i)) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) < V) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) = x 0 :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc 0)
    rw [he] at hs
    by_cases hi : i = 0
    · subst i
      simpa [stripeUpper] using And.intro (hc 0).1 hs
    · simpa [stripeUpper, hi] using hc i
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := by
      intro i
      have hh := hx i (mem_univ i)
      by_cases hi : i = 0
      · subst i
        simp only [stripeUpper, Function.update_self, mem_Ico] at hh
        exact ⟨hh.1, lt_of_lt_of_le hh.2 hV.2⟩
      · simpa [stripeUpper, hi] using hh
    refine ⟨hc, ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc 0)]
    simpa [stripeUpper] using (hx 0 (mem_univ 0)).2

lemma volume_stripe {V : ℝ} (hV : V ∈ Icc 0 1) :
    torusVolume (stripe V) = ENNReal.ofReal V := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_stripe V),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_stripe V)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter (measurable_quotientMap (measurableSet_stripe V))).nullMeasurableSet)
  rw [stripe_lift_preimage hV] at hm
  rw [← hm, Real.volume_pi_Ico]
  norm_num [stripeUpper, Fin.prod_univ_succ]

lemma integral_divergence_stripe {V : ℝ} (hV : V ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' stripe V, divergence F x) =
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let b := stripeUpper V
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hb : ∀ i, (0 : Fin 3 → ℝ) i ≤ b i := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [b, stripeUpper] using hV.1
    · simp [b, stripeUpper, hi]
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) b hb g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : ∀ i : Fin 3, i ≠ 0 →
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth (b i) x)) -
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth 0 x)) = 0 := by
    intro i hi
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth (b i) x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      have hbi : b i = 1 := by simp [b, stripeUpper, hi]
      rw [hbi]
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  simp only [Pi.zero_apply] at hth
  rw [Finset.sum_eq_single 0 (fun i _ hi => hzero i hi) (by simp)] at hth
  have hab : b ∘ (0 : Fin 3).succAbove = (1 : Fin 2 → ℝ) := by
    ext i
    simp [b, stripeUpper]
  have ha0 : (0 : Fin 3 → ℝ) ∘ (0 : Fin 3).succAbove = (0 : Fin 2 → ℝ) := rfl
  rw [hab, ha0] at hth
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, stripe_lift_preimage hV]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  rw [← volume_pi]
  convert hth using 1 <;> simp [g, b, stripeUpper, e]
  rfl

end CubicTorus

namespace CubicTorus

lemma volume_square_face : volume (Icc (0 : Fin 2 → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]
  norm_num

lemma stripe_flux_bound {F : Cover → Cover} (hF : AdmissibleField F) (a : ℝ) :
    |∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x)) 0| ≤ 1 := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (show volume (Icc (0 : Fin 2 → ℝ) 1) < ⊤ by rw [volume_square_face]; norm_num)
    (fun x (_ : x ∈ Icc (0 : Fin 2 → ℝ) 1) =>
      (PiLp.norm_apply_le (F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x))) 0).trans (hF.2.2 _))
  simpa only [Real.norm_eq_abs, Measure.real, volume_square_face, ENNReal.toReal_one, mul_one] using hh

theorem perimeter_stripe_le {V : ℝ} (hV : V ∈ Icc 0 1) : perimeter (stripe V) ≤ 2 := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [integral_divergence_stripe hV hF]
  have hupper := (abs_le.1 (stripe_flux_bound hF V)).2
  have hlower := (abs_le.1 (stripe_flux_bound hF 0)).1
  have hh : (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) ≤ 2 := by linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by norm_num)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem exists_isMinimizerAt {V : ℝ} (hV : V ∈ Ioo 0 1) :
    ∃ E : Set Torus, IsMinimizerAt V E := by
  let S : Set ℝ≥0∞ := {p | ∃ E : Set Torus, MeasurableSet E ∧
    torusVolume E = ENNReal.ofReal V ∧ perimeter E = p ∧ p ≤ 2}
  have hV' : V ∈ Icc (0 : ℝ) 1 := ⟨hV.1.le, hV.2.le⟩
  have hne : S.Nonempty := ⟨perimeter (stripe V), stripe V, measurableSet_stripe V,
    volume_stripe hV', rfl, perimeter_stripe_le hV'⟩
  have hinf : sInf S ≤ 2 := (sInf_le hne.choose_spec).trans hne.choose_spec.choose_spec.2.2.2
  obtain ⟨ps, _, hconv, hps⟩ := exists_seq_tendsto_sInf hne (OrderBot.bddBelow S)
  choose Es hEs hvol hpEq hpBound using hps
  have hbound : ∀ n, perimeter (Es n) ≤ ENNReal.ofReal 2 := by
    intro n
    rw [hpEq n]
    simpa using hpBound n
  obtain ⟨E, hE, ns, hns, hae⟩ := exists_ae_tendsto_characteristic hEs (by norm_num) hbound
  have hvo : torusVolume E = ENNReal.ofReal V := by
    have ht := tendsto_volume_of_ae_tendsto (fun n => (hEs (ns n)).nullMeasurableSet)
      hE.nullMeasurableSet hae
    have hc : Tendsto (fun n => torusVolume (Es (ns n))) atTop (𝓝 (ENNReal.ofReal V)) := by
      simpa only [hvol] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ENNReal.ofReal V) atTop _)
    exact tendsto_nhds_unique ht hc
  have hpe : perimeter E ≤ sInf S :=
    perimeter_le_of_ae_tendsto_bound (fun n => (hEs (ns n)).nullMeasurableSet)
      hE.nullMeasurableSet hae (fun n => (hpEq (ns n)).le) (hconv.comp hns.tendsto_atTop)
  refine ⟨E, ⟨hE.nullMeasurableSet, (hpe.trans hinf).trans_lt (by norm_num)⟩, hvo, ?_⟩
  intro F hF hFv
  by_cases hFp : perimeter F ≤ 2
  · have hrep := hF.1.toMeasurable_ae_eq
    have hex : perimeter F ∈ S := by
      refine ⟨toMeasurable torusVolume F, measurableSet_toMeasurable _ _, ?_, ?_, hFp⟩
      · exact (measure_congr hrep).trans hFv
      · exact perimeter_congr_ae hrep
    exact hpe.trans (sInf_le hex)
  · exact (hpe.trans hinf).trans (le_of_lt (lt_of_not_ge hFp))

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
open scoped Topology

lemma isoperimetricProfile_eq_of_isMinimizerAt {V : ℝ} {E : Set Torus}
    (hE : IsMinimizerAt V E) : isoperimetricProfile V = (perimeter E).toReal / 2 := by
  have heq : sInf {p : ℝ≥0∞ | ∃ F : Set Torus,
      FinitePerimeter F ∧ torusVolume F = ENNReal.ofReal V ∧ perimeter F = p} = perimeter E := by
    apply le_antisymm
    · exact sInf_le ⟨E, hE.1, hE.2.1, rfl⟩
    · apply le_sInf
      rintro p ⟨F, hF, hFv, rfl⟩
      exact hE.2.2 F hF hFv
  simp only [isoperimetricProfile, heq]

lemma isoperimetricProfile_nonneg (V : ℝ) : 0 ≤ isoperimetricProfile V :=
  div_nonneg ENNReal.toReal_nonneg (by norm_num)

lemma isoperimetricProfile_pos {V : ℝ} (hV : V ∈ Ioo 0 1) :
    0 < isoperimetricProfile V := by
  obtain ⟨E, hE⟩ := exists_isMinimizerAt hV
  rw [isoperimetricProfile_eq_of_isMinimizerAt hE]
  exact div_pos (ENNReal.toReal_pos (perimeter_pos_of_volume hV hE.1.1 hE.2.1).ne'
    hE.1.2.ne) (by norm_num)

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

lemma second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y => f y - g y)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have heq : deriv (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => deriv f y - deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_sub (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_sub
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

lemma jet_comparison {I C F : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMin (fun y => I y - F y) x) :
    deriv C x = deriv F x ∧ deriv (deriv F) x ≤ deriv (deriv C) x := by
  have hmc : IsLocalMin (fun y => C y - F y) x := by
    filter_upwards [hm, hs.above] with y hy habove
    change C x - F x ≤ C y - F y
    rw [hs.contact]
    linarith
  have h1 := hmc.deriv_eq_zero
  change deriv (C - F) x = 0 at h1
  rw [deriv_sub (hs.smooth.differentiableAt (by norm_num))
    (hF.differentiableAt (by norm_num))] at h1
  have h2 := second_deriv_nonneg_of_local_min hmc (hs.smooth.continuousAt.sub hF.continuousAt)
  rw [second_deriv_sub hs.smooth hF] at h2
  exact ⟨sub_eq_zero.mp h1, sub_nonneg.mp h2⟩

lemma second_deriv_quadratic (α β γ x : ℝ) :
    deriv (deriv (fun y => α * y ^ 2 + β * y + γ)) x = 2 * α := by
  have hd (y : ℝ) : HasDerivAt (fun z => α * z ^ 2 + β * z + γ) (2 * α * y + β) y := by
    convert! (((hasDerivAt_pow 2 y).const_mul α).add
      ((hasDerivAt_id y).const_mul β)).add_const γ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdeq : deriv (fun y => α * y ^ 2 + β * y + γ) = (fun y => 2 * α * y + β) := by
    funext y
    exact (hd y).deriv
  rw [hdeq]
  have hd2 : HasDerivAt (fun y : ℝ => 2 * α * y + β) (2 * α) x := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul (2 * α)).add_const β
  exact hd2.deriv

end CubicTorus.Reduction

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus.Reduction

theorem chord_below_of_lowerSemicontinuous_upper_support {I : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : LowerSemicontinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) :
    ∀ x ∈ Icc a b, I a + (x - a) * (I b - I a) / (b - a) ≤ I x := by
  intro c hc
  by_contra! hgap
  let m := (I b - I a) / (b - a)
  let L := fun x : ℝ => I a + (x - a) * m
  have hLa : L a = I a := by simp [L]
  have hLb : L b = I b := by
    dsimp [L, m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hgap' : I c < L c := by simpa [L, m, mul_div_assoc] using hgap
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    intro heq
    subst c
    rw [hLa] at hgap'
    exact (lt_irrefl _ hgap')
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    intro heq
    subst c
    rw [hLb] at hgap'
    exact (lt_irrefl _ hgap')
  let ε := (L c - I c) / (2 * ((c - a) * (b - c)))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap')
    (mul_pos (by norm_num) (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hcb)))
  let F := fun x : ℝ => ε * x ^ 2 + (m - ε * (a + b)) * x +
    (I a - a * m + ε * a * b)
  have hF_eq (x : ℝ) : F x = L x + ε * (x - a) * (x - b) := by dsimp [F, L]; ring
  have hFa : F a = I a := by rw [hF_eq, hLa]; ring
  have hFb : F b = I b := by rw [hF_eq, hLb]; ring
  have hFc : I c < F c := by
    have hprod : ε * (c - a) * (b - c) = (L c - I c) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt (sub_pos.mpr hca), ne_of_gt (sub_pos.mpr hcb)]
    rw [hF_eq]
    nlinarith
  have hF : ContDiff ℝ 2 F := by dsimp [F]; fun_prop
  have hsemi : LowerSemicontinuousOn (fun y ↦ I y-F y) (Icc a b) := by
    simpa only [sub_eq_add_neg,Pi.neg_apply] using hI.add hF.continuous.neg.continuousOn.lowerSemicontinuousOn
  obtain ⟨x, hx, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (nonempty_Icc.mpr hab.le) isCompact_Icc hsemi
  have hneg : I x - F x < 0 := lt_of_le_of_lt (hmin hc) (sub_neg.mpr hFc)
  have hxa : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro heq
    subst x
    rw [hFa, sub_self] at hneg
    exact lt_irrefl _ hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro heq
    subst x
    rw [hFb, sub_self] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨C, hC, hC''⟩ := hsupport x ⟨hxa, hxb⟩
  have hj := (jet_comparison hC hF.contDiffAt
    (hmin.isLocalMin (Icc_mem_nhds hxa hxb))).2
  have hF'' : deriv (deriv F) x = 2 * ε := second_deriv_quadratic _ _ _ _
  rw [hF''] at hj
  linarith

end CubicTorus.Reduction

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem concaveOn_isoperimetricProfile_three_halves :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun V ↦ isoperimetricProfile V^(3/2 : ℝ)) := by
  let J : ℝ → ℝ := fun V ↦ isoperimetricProfile V^(3/2 : ℝ)
  have hJ : ContinuousOn J (Icc (0 : ℝ) 1) := by
    exact (Real.continuous_rpow_const (by norm_num : 0≤(3/2 : ℝ))).comp_continuousOn
      continuousOn_isoperimetricProfile
  have hchord {a b : ℝ} (ha : 0≤a) (hb : b≤1) (hab : a<b) :
      ∀ x∈Icc a b,J a+(x-a)*(J b-J a)/(b-a)≤J x := by
    apply Reduction.chord_below_of_lowerSemicontinuous_upper_support hab
    · exact hJ.lowerSemicontinuousOn.mono (Icc_subset_Icc ha hb)
    · intro x hx
      exact isoperimetricProfile_power_upper_support ⟨ha.trans_lt hx.1,hx.2.trans_le hb⟩
  change ConcaveOn ℝ (Icc (0 : ℝ) 1) J
  apply LinearOrder.concaveOn_of_lt (convex_Icc (0 : ℝ) 1)
  intro x hx y hy hxy a b ha hb hab
  have hmem : a*x+b*y∈Icc x y := by
    have hax : a*x+b*x=x := by rw [← add_mul,hab,one_mul]
    have hay : a*y+b*y=y := by rw [← add_mul,hab,one_mul]
    constructor <;> nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxy.le),
      mul_nonneg hb.le (sub_nonneg.mpr hxy.le)]
  have hh := hchord hx.1 hy.2 hxy (a*x+b*y) hmem
  have he : J x+(a*x+b*y-x)*(J y-J x)/(y-x)=a*J x+b*J y := by
    have ha' : a=1-b := by linarith
    rw [ha']
    field_simp [sub_ne_zero.mpr hxy.ne']
    ring
  rw [he] at hh
  exact hh

end CubicTorus

end
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
namespace Reduction

lemma UpperSupport.deriv_le_left_secant {I C : ℝ → ℝ} {a V : ℝ}
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) I) (ha : 0≤a) (hV : V≤1)
    (haV : a<V) (hs : UpperSupport I C V) :
    deriv C V≤(I V-I a)/(V-a) := by
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto ht
  filter_upwards [hs.above.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ W in 𝓝 V, a<W from Ioi_mem_nhds haV).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with W hW haW hWV
  have hv : V∈Icc (0 : ℝ) 1 := ⟨ha.trans haV.le,hV⟩
  have ha' : a∈Icc (0 : ℝ) 1 := ⟨ha,haV.le.trans hV⟩
  have hw : W∈Icc (0 : ℝ) 1 := ⟨ha.trans haW.le,hWV.le.trans hV⟩
  have hm := hc.antitoneOn_slope_lt hv ⟨ha',haV⟩ ⟨hw,hWV⟩ haW.le
  have he : slope I V a=(I V-I a)/(V-a) := by
    rw [slope_def_field]
    apply (div_eq_div_iff (sub_ne_zero.mpr haV.ne) (sub_ne_zero.mpr haV.ne')).mpr
    ring
  have hcomp : slope C V W ≤ slope I V W := by
    simp only [slope_def_field,hs.contact]
    exact div_le_div_of_nonpos_of_le (sub_nonpos.mpr hWV.le) (sub_le_sub_right hW _)
  exact hcomp.trans (hm.trans_eq he)

lemma UpperSupport.power_three_halves_contact {I C : ℝ → ℝ} {V : ℝ}
    (hs : UpperSupport I C V) (hI : ∀ W,0≤I W) (hp : 0<I V) :
    UpperSupport (fun W ↦ I W^(3/2 : ℝ)) (fun W ↦ C W^(3/2 : ℝ)) V := by
  have hc : 0<C V := hs.contact ▸ hp
  refine ⟨hs.smooth.rpow_const_of_ne hc.ne',by rw [hs.contact],?_⟩
  filter_upwards [hs.above] with W hW
  exact Real.rpow_le_rpow (hI W) hW (by norm_num)

end Reduction

theorem profile_upper_support_power_secant_oai {a V : ℝ} (ha : 0≤a) (hV : V∈Ioo 0 1)
    (haV : a<V) {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    (3/2 : ℝ)*deriv C V*Real.sqrt (isoperimetricProfile V) ≤
      (isoperimetricProfile V^(3/2 : ℝ)-isoperimetricProfile a^(3/2 : ℝ))/(V-a) := by
  have hp := isoperimetricProfile_pos hV
  have hsp := hs.power_three_halves_contact isoperimetricProfile_nonneg hp
  have hh := hsp.deriv_le_left_secant concaveOn_isoperimetricProfile_three_halves ha hV.2.le haV
  have hc : C V≠0 := ne_of_gt (hs.contact ▸ hp)
  rw [deriv_rpow_const (hs.smooth.differentiableAt (by norm_num)) (Or.inl hc),hs.contact] at hh
  norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num] at hh
  rw [←Real.sqrt_eq_rpow] at hh
  nlinarith only [hh]

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.profile_upper_support_power_secant_oai := @OAI.CubicTorus.profile_upper_support_power_secant_oai
