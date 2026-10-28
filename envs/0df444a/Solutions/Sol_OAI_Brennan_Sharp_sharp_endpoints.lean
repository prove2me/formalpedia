-- Prove2me | solution 1 for OAI.Brennan.Sharp.sharp_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:00:21.917192+00:00
-- url     : https://prove2.me/submissions/02dac5ea-bfc6-4741-9e69-e797783ba6d9

import Mathlib
import Definitions.Def_BrennanSharp

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_LogIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma determinant_complex_real (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re*(A Complex.I).im-(A Complex.I).re*(A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

end Brennan

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_UnivalentArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma det_fderiv_complex {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2 := by
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,determinant_complex_real,
    ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    Complex.I_mul, Complex.normSq_apply]
  ring

end Brennan

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma nonconstant_germ_of_injOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : Set.InjOn f U) {a : ℂ} (ha : a ∈ U) :
    ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have heq : ∀ᶠ z in 𝓝 a, z = a := by
    filter_upwards [hc, hU.mem_nhds ha] with z hz hzU
    exact hf hzU ha hz
  have heq' : ∀ᶠ z in 𝓝[≠] a, z = a := heq.filter_mono nhdsWithin_le_nhds
  have hne' : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
  obtain ⟨z, hz, hne⟩ := (heq'.and hne').exists
  exact hne hz

lemma univalent_inverse_continuousAt {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f a) := by
  have haan : AnalyticAt ℂ f a := (hf.1.analyticOnNhd hU) a ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    haan.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hl : ∀ᶠ z in 𝓝 a, Function.invFunOn f U (f z) = z := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have ht : Tendsto (Function.invFunOn f U ∘ f) (𝓝 a) (𝓝 a) :=
    tendsto_id.congr' (Filter.EventuallyEq.symm hl)
  rw [ContinuousAt, hf.2.leftInvOn_invFunOn ha]
  exact (tendsto_map'_iff.mpr ht).mono_left hopen

lemma univalent_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  have han : AnalyticAt ℂ f a := hf.1.analyticOnNhd hU a ha
  have hd_nonconst : ¬ ∀ᶠ z in 𝓝 a, deriv f z = 0 := by
    intro hc
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hc.and (hU.mem_nhds ha))
    have hfball : DifferentiableOn ℂ f (Metric.ball a r) :=
      hf.1.mono (fun z hz => (hball hz).2)
    have hcball : ∀ z ∈ Metric.ball a r, f z = f a := by
      intro z hz
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
        hfball (fun w hw => (hball hw).1) hz (Metric.mem_ball_self hr)
    apply nonconstant_germ_of_injOn hU hf.2 ha
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    exact hcball z hz
  have hd : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    han.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left hd_nonconst
  let g := Function.invFunOn f U
  have hgc : ContinuousAt g (f a) := univalent_inverse_continuousAt hU hf ha
  have hga : g (f a) = a := hf.2.leftInvOn_invFunOn ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hright : ∀ᶠ w in 𝓝 (f a), g w ∈ U ∧ f (g w) = w := by
    apply (hopen (Filter.mem_map.mpr ?_))
    filter_upwards [hU.mem_nhds ha] with z hz
    exact ⟨Function.invFunOn_apply_mem hz, Function.invFunOn_apply_eq hz⟩
  have hgne : ∀ᶠ w in 𝓝[≠] (f a), g w ≠ a := by
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwne
    intro heq
    exact hwne (hw.2.symm.trans (congrArg f heq))
  have hgt : Tendsto g (𝓝[≠] (f a)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hgne⟩
    simpa only [hga] using (hgc.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto g (𝓝[≠] (f a)) (𝓝 (g (f a))))
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
    filter_upwards [hgt.eventually hd, hright.filter_mono nhdsWithin_le_nhds]
      with w hwder hw
    have hwan : AnalyticAt ℂ f (g w) := hf.1.analyticOnNhd hU (g w) hw.1
    have hws : HasStrictDerivAt f (deriv f (g w)) (g w) :=
      (hwan.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hl : ∀ᶠ z in 𝓝 (g w), g (f z) = z := by
      filter_upwards [hU.mem_nhds hw.1] with z hz
      exact hf.2.leftInvOn_invFunOn hz
    simpa [hw.2] using (hws.to_local_left_inverse hwder hl).hasDerivAt.differentiableAt
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hgd hgc
  have hcomp := hgan.differentiableAt.hasDerivAt.comp a han.differentiableAt.hasDerivAt
  have hid : (fun z => g (f z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have hprod : deriv g (f a) * deriv f a = 1 := by
    simpa using (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod

end Brennan

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_Koebe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma one_sub_ne_zero_disk {z : ℂ} (hz : z ∈ disk) : 1-z ≠ 0 := by
  have h : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have : z = 1 := by linear_combination -he
  simp [this] at h

lemma koebeMap_hasDerivAt {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt koebeMap ((1+z)/(1-z)^3) z := by
  have hn := one_sub_ne_zero_disk hz
  have h := (hasDerivAt_id z).div (((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).pow 2) (pow_ne_zero 2 hn)
  convert h using 1 <;> try rfl
  dsimp
  field_simp [hn]
  ring

lemma koebeMap_schlicht : Schlicht koebeMap := by
  refine ⟨⟨fun z hz => (koebeMap_hasDerivAt hz).differentiableAt.differentiableWithinAt,?_⟩,by simp [koebeMap],?_⟩
  · intro z hz w hw he
    have hnz := one_sub_ne_zero_disk hz
    have hnw := one_sub_ne_zero_disk hw
    have he' : (z-w)*(1-z*w) = 0 := by
      have hh := (div_eq_div_iff (pow_ne_zero 2 hnz) (pow_ne_zero 2 hnw)).mp he
      linear_combination hh
    have hzw : 1-z*w ≠ 0 := by
      have hz' : ‖z‖ < 1 := by simpa [disk] using hz
      have hw' : ‖w‖ < 1 := by simpa [disk] using hw
      have hn : ‖z*w‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg z,norm_nonneg w]
      intro h
      have : z*w = 1 := by linear_combination -h
      simp [this] at hn
    exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hzw)
  · simpa using (koebeMap_hasDerivAt (show (0:ℂ) ∈ disk by simp [disk])).deriv

end Brennan

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_DomainArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma univalent_inverse_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : UnivalentOn φ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (Function.invFunOn φ U) (deriv φ z)⁻¹ (φ z) := by
  have ha := hφ.1.analyticOnNhd hU z hz
  apply (ha.hasStrictDerivAt.to_local_left_inverse (univalent_deriv_ne_zero hU hφ hz) ?_).hasDerivAt
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hφ.2.leftInvOn_invFunOn hw

lemma conformal_lintegral_eq {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, b w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
  have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
  dsimp only
  have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
  rw [hf,hd',abs_of_nonneg (sq_nonneg _)]

end Brennan

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_AffineArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma lintegral_affine_unit (a u : ℂ) (hu : ‖u‖ = 1) (f : ℂ → ℝ≥0∞) :
    (∫⁻ w, f (a + u * w)) = ∫⁻ z, f z := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  let F : ℂ → ℂ := fun w => a + u * w
  have hd (w : ℂ) : HasDerivAt F u w := by
    exact (hasDerivAt_const_mul (x := w) u).const_add a
  have hinj : InjOn F univ := by
    intro x _ y _ h
    change a + u * x = a + u * y at h
    exact mul_left_cancel₀ hu0 (add_left_cancel h)
  have himage : F '' univ = univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine ⟨(z - a) / u, Set.mem_univ _, ?_⟩
    dsimp [F]
    field_simp [hu0]
    ring
  have he := conformal_lintegral_eq MeasurableSet.univ
    (fun z _ => (hd z).differentiableAt) hinj f
  rw [himage] at he
  have hder (z : ℂ) : deriv F z = u := (hd z).deriv
  simp only [setLIntegral_univ, hder, hu, one_pow, ENNReal.ofReal_one, one_mul] at he
  exact he.symm

lemma lintegral_left_disk_indicator (t : ℝ) :
    (∫⁻ w, disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)) (-1 + w)) =
      areaMoment koebeMap disk t := by
  have h := lintegral_affine_unit (-1) 1 (by simp)
    (disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)))
  have hdisk : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [lintegral_indicator hdisk] at h
  simpa only [one_mul, areaMoment] using h

lemma lintegral_right_disk_indicator (t : ℝ) :
    (∫⁻ w, disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)) (1 - w)) =
      areaMoment koebeMap disk t := by
  have h := lintegral_affine_unit 1 (-1) (by simp)
    (disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)))
  have hdisk : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [lintegral_indicator hdisk] at h
  simpa only [neg_one_mul, ← sub_eq_add_neg, areaMoment] using h

end Brennan.Sharp

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_KoebeReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_deriv_norm_left {w : ℂ} (hz : -1 + w ∈ disk) :
    ‖deriv koebeMap (-1 + w)‖ = ‖w‖ / ‖2 - w‖ ^ 3 := by
  rw [(koebeMap_hasDerivAt hz).deriv]
  have hnum : 1 + (-1 + w) = w := by ring
  have hden : 1 - (-1 + w) = 2 - w := by ring
  rw [hnum, hden, norm_div, norm_pow]

lemma koebe_deriv_norm_right {w : ℂ} (hz : 1 - w ∈ disk) :
    ‖deriv koebeMap (1 - w)‖ = ‖2 - w‖ / ‖w‖ ^ 3 := by
  rw [(koebeMap_hasDerivAt hz).deriv]
  have hnum : 1 + (1 - w) = 2 - w := by ring
  have hden : 1 - (1 - w) = w := by ring
  rw [hnum, hden, norm_div, norm_pow]

lemma one_le_norm_two_sub {w : ℂ} (hw : ‖w‖ < 1 / 2) :
    1 ≤ ‖2 - w‖ := by
  have h := norm_sub_norm_le (2 : ℂ) w
  norm_num at h
  linarith

lemma koebe_negative_endpoint_lower {w : ℂ}
    (hz : -1 + w ∈ disk) (hw : ‖w‖ < 1 / 2) :
    ‖w‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap (-1 + w)‖ ^ (-2 : ℝ) := by
  have hd : 0 < ‖deriv koebeMap (-1 + w)‖ :=
    norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball koebeMap_schlicht.1 hz)
  have hb : ‖deriv koebeMap (-1 + w)‖ ≤ ‖w‖ := by
    rw [koebe_deriv_norm_left hz]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_norm_two_sub hw))
  exact Real.rpow_le_rpow_of_nonpos hd hb (by norm_num)

lemma koebe_positive_endpoint_lower {w : ℂ}
    (hz : 1 - w ∈ disk) (h0 : 0 < ‖w‖) (hw : ‖w‖ < 1 / 2) :
    ‖w‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap (1 - w)‖ ^ (2 / 3 : ℝ) := by
  have hb : 1 / ‖w‖ ^ 3 ≤ ‖deriv koebeMap (1 - w)‖ := by
    rw [koebe_deriv_norm_right hz]
    exact div_le_div_of_nonneg_right (one_le_norm_two_sub hw) (by positivity)
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / ‖w‖ ^ 3) hb
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have he : (1 / ‖w‖ ^ 3) ^ (2 / 3 : ℝ) = ‖w‖ ^ (-2 : ℝ) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast ‖w‖ 3,
      ← Real.rpow_mul h0.le]
    norm_num [Real.rpow_neg, Real.rpow_two]
  rwa [he] at hp

end Brennan.Sharp

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_InverseMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_inverse_areaMoment (s : ℝ) :
    areaMoment koebeInverse koebeDomain s = areaMoment koebeMap disk (2 - s) := by
  have hdisk : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  have hopen : IsOpen disk := Metric.isOpen_ball
  unfold areaMoment koebeDomain
  rw [conformal_lintegral_eq (F := koebeMap) (s := disk) hdisk
    (fun z hz => (koebeMap_hasDerivAt hz).differentiableAt)
    koebeMap_schlicht.1.2]
  apply setLIntegral_congr_fun hdisk
  intro z hz
  change ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 : ℕ)) *
    ENNReal.ofReal (‖deriv koebeInverse (koebeMap z)‖ ^ s) =
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 - s))
  have hderiv : deriv koebeInverse (koebeMap z) = (deriv koebeMap z)⁻¹ :=
    (univalent_inverse_hasDerivAt hopen koebeMap_schlicht.1 hz).deriv
  rw [hderiv, norm_inv, Real.inv_rpow (norm_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hn : 0 < ‖deriv koebeMap z‖ :=
    norm_pos_iff.mpr (univalent_deriv_ne_zero hopen koebeMap_schlicht.1 hz)
  rw [← Real.rpow_natCast ‖deriv koebeMap z‖ 2,
    ← Real.rpow_neg hn.le, ← Real.rpow_add hn]
  rfl

lemma not_integrable_of_areaMoment_top {f : ℂ → ℂ} {U : Set ℂ} {t : ℝ}
    (h : areaMoment f U t = ⊤) :
    ¬ IntegrableOn (fun z => ‖deriv f z‖ ^ t) U volume := by
  intro hi
  have hf := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun z : ℂ => Real.rpow_nonneg (norm_nonneg (deriv f z)) t))).mp hi.hasFiniteIntegral
  change areaMoment f U t < ⊤ at hf
  rw [h] at hf
  exact lt_irrefl _ hf

end Brennan.Sharp

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_KoebeCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Brennan.Sharp

lemma right_cone_mem_disk {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) : 1 - w ∈ disk := by
  have hsq : ‖1 - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hsmall' : ‖w‖ ^ 2 < ‖w‖ := by nlinarith
  have hnorm : ‖1 - w‖ < 1 := by
    nlinarith [norm_nonneg (1 - w)]
  simpa only [disk, Metric.mem_ball, dist_zero_right] using hnorm

lemma left_cone_mem_disk {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) : -1 + w ∈ disk := by
  have hr := right_cone_mem_disk h0 hsmall hcone
  have hid : (-1 : ℂ) + w = -(1 - w) := by ring
  simpa only [disk, Metric.mem_ball, dist_zero_right, hid, norm_neg] using hr

lemma norm_rpow_neg_two (w : ℂ) :
    ‖w‖ ^ (-2 : ℝ) = 1 / ‖w‖ ^ 2 := by
  simpa only [Real.rpow_two, one_div] using
    Real.rpow_neg (norm_nonneg w) (2 : ℝ)

lemma koebe_left_cone_lower {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) :
    1 / ‖w‖ ^ 2 ≤ ‖deriv koebeMap (-1 + w)‖ ^ (-2 : ℝ) := by
  rw [← norm_rpow_neg_two]
  exact koebe_negative_endpoint_lower (left_cone_mem_disk h0 hsmall hcone) hsmall

lemma koebe_right_cone_lower {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) :
    1 / ‖w‖ ^ 2 ≤ ‖deriv koebeMap (1 - w)‖ ^ (2 / 3 : ℝ) := by
  rw [← norm_rpow_neg_two]
  exact koebe_positive_endpoint_lower (right_cone_mem_disk h0 hsmall hcone) h0 hsmall

end Brennan.Sharp

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_KoebePolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Brennan.Sharp

lemma sector_cos_lower {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    (1 : ℝ) / 2 ≤ Real.cos θ := by
  have habs : |θ| ≤ Real.pi / 3 :=
    (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) habs
  simpa only [Real.cos_pi_div_three, Real.cos_abs] using h

lemma polar_cone_data {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    ‖Complex.polarCoord.symm (r, θ)‖ = r ∧
      ‖Complex.polarCoord.symm (r, θ)‖ / 2 ≤
        (Complex.polarCoord.symm (r, θ)).re := by
  have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
    simpa only [abs_of_pos hr] using Complex.norm_polarCoord_symm (r, θ)
  refine ⟨hn, ?_⟩
  have hre : (Complex.polarCoord.symm (r, θ)).re = r * Real.cos θ := by
    rw [Complex.polarCoord_symm_apply]
    simp [Complex.cos_ofReal_re]
  rw [hn, hre]
  have hmul := mul_le_mul_of_nonneg_left (sector_cos_lower hθ) hr.le
  nlinarith

lemma polar_left_mem_disk {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    -1 + Complex.polarCoord.symm (r, θ) ∈ disk := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  exact left_cone_mem_disk (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc

lemma polar_right_mem_disk {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    1 - Complex.polarCoord.symm (r, θ) ∈ disk := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  exact right_cone_mem_disk (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc

lemma koebe_polar_left_lower {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    1 / r ^ 2 ≤ ‖deriv koebeMap (-1 + Complex.polarCoord.symm (r, θ))‖ ^ (-2 : ℝ) := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  have h := koebe_left_cone_lower (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc
  simpa only [hn] using h

lemma koebe_polar_right_lower {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    1 / r ^ 2 ≤ ‖deriv koebeMap (1 - Complex.polarCoord.symm (r, θ))‖ ^ (2 / 3 : ℝ) := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  have h := koebe_right_cone_lower (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc
  simpa only [hn] using h

end Brennan.Sharp

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_SectorDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Brennan.Sector

theorem lintegral_inv_Ioo_eq_top (R : ℝ) (hR : 0 < R) :
    (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal r⁻¹) = ⊤ := by
  by_contra h
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) R)] (fun r : ℝ => r⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact inv_nonneg.mpr hr.1.le
  have hf : HasFiniteIntegral (fun r : ℝ => r⁻¹) (volume.restrict (Ioo (0 : ℝ) R)) :=
    (hasFiniteIntegral_iff_ofReal hn).2 (lt_top_iff_ne_top.mpr h)
  have hi : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo (0 : ℝ) R) :=
    ⟨measurable_inv.aestronglyMeasurable, hf⟩
  have hp : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo (0 : ℝ) R) := by
    simpa only [Real.rpow_neg_one] using hi
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hR).mp hp)

theorem lintegral_eq_top_of_sector_lower_bound (f : ℂ → ℝ≥0∞)
    (R a b c : ℝ) (hR : 0 < R) (hab : a < b) (hc : 0 < c)
    (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi)
    (hlower : ∀ r ∈ Ioo (0 : ℝ) R, ∀ θ ∈ Ioo a b,
      ENNReal.ofReal (c / r ^ 2) ≤ f (Complex.polarCoord.symm (r, θ))) :
    (∫⁻ z, f z) = ⊤ := by
  let box : Set (ℝ × ℝ) := Ioo (0 : ℝ) R ×ˢ Ioo a b
  let radial : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal c * ENNReal.ofReal p.1⁻¹
  have hradial : Measurable radial :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_fst.inv)
  have hcinv : (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal c * ENNReal.ofReal r⁻¹) = ⊤ := by
    have hmeas : Measurable (fun r : ℝ => ENNReal.ofReal r⁻¹) :=
      ENNReal.measurable_ofReal.comp measurable_inv
    rw [lintegral_const_mul (ENNReal.ofReal c) hmeas,
      lintegral_inv_Ioo_eq_top R hR,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]
  have hbox : (∫⁻ p in box, radial p) = ⊤ := by
    change (∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo a b, radial p ∂volume.prod volume) = ⊤
    rw [setLIntegral_prod_symm _ hradial.aemeasurable]
    simp only [radial, hcinv]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))]
  have hsub : box ⊆ polarCoord.target := by
    rw [polarCoord_target]
    intro p hp
    exact ⟨hp.1.1, lt_of_le_of_lt ha hp.2.1, lt_of_lt_of_le hp.2.2 hb⟩
  have hlower' (p : ℝ × ℝ) (hp : p ∈ box) :
      radial p ≤ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) := by
    have hr : 0 < p.1 := hp.1.1
    have hid : ENNReal.ofReal c * ENNReal.ofReal p.1⁻¹ =
        ENNReal.ofReal p.1 * ENNReal.ofReal (c / p.1 ^ 2) := by
      rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hr.le]
      congr 1
      field_simp [ne_of_gt hr]
    change ENNReal.ofReal c * ENNReal.ofReal p.1⁻¹ ≤
      ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)
    rw [hid]
    exact mul_le_mul_right (hlower p.1 hp.1 p.2 hp.2) _
  apply top_unique
  calc
    ⊤ = ∫⁻ p in box, radial p := hbox.symm
    _ ≤ ∫⁻ p in box, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
      setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Ioo) hlower'
    _ ≤ ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
      lintegral_mono_set hsub
    _ = ∫⁻ z, f z := Complex.lintegral_comp_polarCoord_symm f

end Brennan.Sector

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_KoebeDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_negative_endpoint_area : areaMoment koebeMap disk (-2) = ⊤ := by
  have h := Sector.lintegral_eq_top_of_sector_lower_bound
    (fun w => disk.indicator
      (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ))) (-1 + w))
    (1 / 2) (-(Real.pi / 3)) (Real.pi / 3) 1
    (by norm_num) (by linarith [Real.pi_pos]) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by
      intro r hr θ hθ
      rw [Set.indicator_of_mem (polar_left_mem_disk hr hθ)]
      exact ENNReal.ofReal_le_ofReal (koebe_polar_left_lower hr hθ))
  rw [lintegral_left_disk_indicator] at h
  exact h

lemma koebe_positive_endpoint_area : areaMoment koebeMap disk (2 / 3) = ⊤ := by
  have h := Sector.lintegral_eq_top_of_sector_lower_bound
    (fun w => disk.indicator
      (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ))) (1 - w))
    (1 / 2) (-(Real.pi / 3)) (Real.pi / 3) 1
    (by norm_num) (by linarith [Real.pi_pos]) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by
      intro r hr θ hθ
      rw [Set.indicator_of_mem (polar_right_mem_disk hr hθ)]
      exact ENNReal.ofReal_le_ofReal (koebe_polar_right_lower hr hθ))
  rw [lintegral_right_disk_indicator] at h
  exact h

end Brennan.Sharp

end

end OAI
end

section
-- module Solutions.OAIW2_BrennanSharp.IntegralMeans_SharpEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_inverse_four_area : areaMoment koebeInverse koebeDomain 4 = ⊤ := by
  rw [koebe_inverse_areaMoment]
  norm_num
  exact koebe_negative_endpoint_area

lemma koebe_inverse_four_thirds_area :
    areaMoment koebeInverse koebeDomain (4 / 3) = ⊤ := by
  rw [koebe_inverse_areaMoment]
  norm_num
  exact koebe_positive_endpoint_area

theorem sharp_endpoints_oai : SharpEndpointStatement := by
  refine ⟨koebeMap_schlicht, koebe_negative_endpoint_area,
    koebe_positive_endpoint_area, ?_, ?_⟩
  · exact not_integrable_of_areaMoment_top koebe_inverse_four_area
  · exact not_integrable_of_areaMoment_top koebe_inverse_four_thirds_area

end Brennan.Sharp

end

end OAI
end

theorem solution : type_of% @OAI.Brennan.Sharp.sharp_endpoints_oai := @OAI.Brennan.Sharp.sharp_endpoints_oai
