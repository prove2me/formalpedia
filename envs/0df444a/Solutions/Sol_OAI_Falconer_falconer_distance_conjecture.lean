-- Prove2me | solution 1 for OAI.Falconer.falconer_distance_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:24:47.736873+00:00
-- url     : https://prove2.me/submissions/0cfe0ea4-b082-4879-9ed6-8d457e55351e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_finite_euclidean_radial_testNorm_moment
import Theorems.Thm_OAI_Falconer_mainTarget_of_three_published_inputs
import Theorems.Thm_OAI_Falconer_publishedPlanarFurstenberg_proved

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_BoundedDualDensity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem exists_bounded_normalized_dual_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hFB : ∀ x, F x ≤ B)
    (hN0 : (∫⁻ x, F x^p ∂μ) ≠ 0) (hNtop : (∫⁻ x, F x^p ∂μ) ≠ ∞) :
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x, h x ≤ C) ∧
      (∫⁻ x, h x^q ∂μ) = 1 ∧
      (∫⁻ x, F x*h x ∂μ) = (∫⁻ x, F x^p ∂μ)^(1/p) := by
  let N := ∫⁻ x, F x^p ∂μ
  let h : X → ℝ≥0∞ := fun x => F x^(p-1) * N^(-1/q)
  have hp1 : 0 < p-1 := sub_pos.mpr (Real.holderConjugate_iff.mp hpq).1
  have hc : N^(-1/q) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hN0 hNtop
  refine ⟨h, by dsimp [h]; fun_prop, ?_, ?_, ?_⟩
  · refine ⟨B^(p-1) * N^(-1/q), ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp1.le hB) hc, ?_⟩
    intro x
    exact mul_le_mul_left (ENNReal.rpow_le_rpow (hFB x) hp1.le) _
  · have he (x : X) : h x^q = F x^p * N⁻¹ := by
      dsimp [h]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,hpq.sub_one_mul_conj]
      rw [show (-1/q)*q = -1 by field_simp [hpq.symm.pos.ne'], ENNReal.rpow_neg_one]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hN0),
      ENNReal.mul_inv_cancel hN0 hNtop]
  · have he (x : X) : F x*h x = F x^p * N^(-1/q) := by
      dsimp [h]
      have hr := ENNReal.rpow_add_of_nonneg (x := F x) 1 (p-1) zero_le_one hp1.le
      rw [show (1 : ℝ)+(p-1)=p by ring, ENNReal.rpow_one] at hr
      rw [← mul_assoc, ← hr]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ hc]
    change N * N^(-1/q) = N^(1/p)
    conv_lhs => lhs; rw [← ENNReal.rpow_one N]
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]
    congr 1
    have ht := hpq.one_div_add_one_div
    norm_num at ht
    simp only [neg_div,one_div]
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteLpIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem continuous_integral_Lp_of_le {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] (hμν : μ ≤ ν)
    {q : ℝ≥0∞} (hq : 1 ≤ q) [Fact (1 ≤ q)] :
    Continuous (fun f : Lp ℝ q ν => ∫ x, f x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro f
  have hmem (g : Lp ℝ q ν) : MemLp g q μ := (Lp.memLp g).mono_measure hμν
  have ht : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) q ν) (𝓝 f) (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' id f).mp tendsto_id
  let C : ℝ≥0∞ := μ univ ^ (1 - 1 / q.toReal)
  have hC : C ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top μ univ)
    by_cases hqt : q = ∞
    · simp [hqt]
    · have hqr : 1 ≤ q.toReal := by exact_mod_cast (ENNReal.toReal_mono hqt hq)
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hqr)
  have htC : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) q ν * C)
      (𝓝 f) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const ht (Or.inr hC)
  have ht1 : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) 1 μ) (𝓝 f) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htC
    · exact fun _ => bot_le
    · intro g
      calc
        eLpNorm (⇑g - ⇑f) 1 μ ≤ eLpNorm (⇑g - ⇑f) q μ * C := by
          simpa [C] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
            ((hmem g).sub (hmem f)).aestronglyMeasurable
        _ ≤ eLpNorm (⇑g - ⇑f) q ν * C :=
          mul_le_mul_left (eLpNorm_mono_measure _ hμν) _
  exact tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) f
    (Eventually.of_forall (fun g => (hmem g).integrable hq)) ht1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_OscillatoryTaylor
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem imaginaryExponential_contDiff : ContDiff ℝ ∞ imaginaryExponential := by
  unfold imaginaryExponential
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

 theorem imaginaryExponential_hasDerivAt (t : ℝ) :
    HasDerivAt imaginaryExponential (Complex.I*imaginaryExponential t) t := by
  unfold imaginaryExponential
  convert (((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).cexp) using 1 <;>
    simp [mul_comm]

 theorem imaginaryExponential_iteratedDeriv (n : ℕ) :
    iteratedDeriv n imaginaryExponential = fun t => Complex.I^n * imaginaryExponential t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [((imaginaryExponential_hasDerivAt t).const_mul (Complex.I^n)).deriv,pow_succ]
    ring

 theorem imaginaryExponential_derivative_norm (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n imaginaryExponential t‖ = 1 := by
  rw [imaginaryExponential_iteratedDeriv]
  simp [imaginaryExponential,Complex.norm_exp,Complex.mul_re]

 theorem imaginaryExponential_taylor_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖imaginaryExponential t - imaginaryTaylor n t‖ ≤ t^(n+1)/(n.factorial:ℝ) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [imaginaryTaylor,imaginaryExponential,zero_pow_eq]
  have hd : UniqueDiffOn ℝ (Icc 0 t) := uniqueDiffOn_Icc ht
  have hs (k : ℕ) : ContDiff ℝ k imaginaryExponential :=
    imaginaryExponential_contDiff.of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
  have hh := taylor_mean_remainder_bound ht.le (hs (n+1)).contDiffOn
    (show t ∈ Icc 0 t from ⟨ht.le,le_rfl⟩) (C := 1) (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hd (hs (n+1)).contDiffAt hy,
        imaginaryExponential_derivative_norm])
  have he : taylorWithinEval imaginaryExponential n (Icc 0 t) 0 t = imaginaryTaylor n t := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv hd (hs k).contDiffAt (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht.le⟩),
      imaginaryExponential_iteratedDeriv]
    simp [imaginaryExponential]
  simpa only [he,sub_zero,one_mul] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianFourier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier pairing in the actual ambient dimension. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem fourier_gaussian_kernel {n : ℕ} {a : ℂ} (ha : 0 < a.re) (ξ : Space n) :
    𝓕 (fun x : Space n => Complex.exp (-a * (‖x‖^2 : ℝ))) ξ =
      gaussianFourierKernel n a ξ := by
  simpa [gaussianFourierKernel, Space] using fourier_gaussian_innerProductSpace ha ξ

theorem gaussian_fourier_pairing {n : ℕ} {a : ℂ} (ha : 0 < a.re)
    (φ : 𝓢(Space n, ℂ)) :
    (∫ x : Space n, Complex.exp (-a * (‖x‖^2 : ℝ)) * 𝓕 φ x) =
      ∫ ξ : Space n, gaussianFourierKernel n a ξ * φ ξ := by
  have hgauss : Integrable (fun x : Space n => Complex.exp (-a * (‖x‖^2 : ℝ))) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add ha 0 (0 : Space n)
  have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Space n)) (μ := volume) (ν := volume)
    (f := fun x : Space n => Complex.exp (-a * (‖x‖^2 : ℝ)))
    (g := (φ : Space n → ℂ))
    Real.continuous_fourierChar continuous_inner hgauss φ.integrable
  have hflip : (innerₗ (Space n)).flip = innerₗ (Space n) := by
    ext x y
    change inner ℝ y x = inner ℝ x y
    exact real_inner_comm _ _
  rw [hflip] at hh
  have he : (∫ x : Space n, Complex.exp (-a * (‖x‖^2 : ℝ)) * 𝓕 φ x) =
      ∫ ξ : Space n, 𝓕 (fun x : Space n =>
        Complex.exp (-a * (‖x‖^2 : ℝ))) ξ * φ ξ := by
    simpa only [smul_eq_mul] using! hh.symm
  rw [he]
  simp only [fourier_gaussian_kernel ha]

theorem gaussian_exponential_norm_le_one {a : ℂ} (ha : 0 ≤ a.re)
    {s : ℝ} (hs : 0 ≤ s) : ‖Complex.exp (-(s : ℂ) / a)‖ ≤ 1 := by
  rw [Complex.norm_exp, div_eq_mul_inv, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
  apply Real.exp_le_one_iff.mpr
  have hi : 0 ≤ a⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg ha (Complex.normSq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hi

theorem gaussianFourierKernel_norm_bound {n : ℕ} {a : ℂ} (ha : 0 ≤ a.re)
    {b : ℝ} (hb : 0 < b) (hn : b ≤ ‖a‖) (ξ : Space n) :
    ‖gaussianFourierKernel n a ξ‖ ≤ (Real.pi / b)^((n : ℝ)/2) := by
  have he : -(Real.pi : ℂ)^2 * (‖ξ‖^2 : ℝ) / a =
      -((Real.pi^2 * ‖ξ‖^2 : ℝ) : ℂ) / a := by push_cast; ring
  have hpow : ‖((Real.pi : ℂ) / a)^((n : ℂ)/2)‖ =
      (Real.pi / ‖a‖)^((n : ℝ)/2) := by
    convert Complex.norm_cpow_real ((Real.pi : ℂ)/a) ((n : ℝ)/2) using 1 <;>
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  unfold gaussianFourierKernel
  rw [norm_mul, hpow, he]
  calc
    _ ≤ (Real.pi / ‖a‖)^((n : ℝ)/2) * 1 :=
      mul_le_mul_of_nonneg_left (gaussian_exponential_norm_le_one ha (by positivity))
        (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left Real.pi_pos.le hb hn) (by positivity)

theorem gaussianFourierKernel_damped_bound {n : ℕ} {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (ξ : Space n) :
    ‖gaussianFourierKernel n ((ε : ℂ) + (b : ℂ)*Complex.I) ξ‖ ≤
      (Real.pi / b)^((n : ℝ)/2) := by
  apply gaussianFourierKernel_norm_bound (by simpa using hε) hb
  simpa [abs_of_pos hb] using
    Complex.abs_im_le_norm ((ε : ℂ) + (b : ℂ)*Complex.I)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_OscillatoryGaussian
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing Gaussian damping while retaining the ambient-dimensional phase. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

theorem gaussianFourierKernel_continuous_damping {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (ξ : Space n) :
    ContinuousAt (fun ε : ℝ =>
      gaussianFourierKernel n ((ε : ℂ) + (b : ℂ)*Complex.I) ξ) 0 := by
  have hne : (b : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') Complex.I_ne_zero
  unfold gaussianFourierKernel
  apply ContinuousAt.mul
  · have ht : ContinuousAt (fun ε : ℝ =>
        (Real.pi : ℂ) / ((ε : ℂ) + (b : ℂ)*Complex.I)) 0 :=
      continuousAt_const.div (by fun_prop) (by simpa using hne)
    have hp : ContinuousAt (fun z : ℂ => z^((n : ℂ)/2))
        ((Real.pi : ℂ) / ((0 : ℂ) + (b : ℂ)*Complex.I)) :=
      Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (by simp [Complex.div_re])) (by simpa using (show 0 < (n : ℝ)/2 by positivity))
    exact hp.comp (f := fun ε : ℝ =>
      (Real.pi : ℂ) / ((ε : ℂ) + (b : ℂ)*Complex.I)) (x := 0) ht
  · apply Complex.continuous_exp.continuousAt.comp
    exact continuousAt_const.div (by fun_prop) (by simpa using hne)

theorem gaussianFourierKernel_integral_limit {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (φ : 𝓢(Space n, ℂ)) :
    Tendsto (fun c : ℝ => ∫ ξ : Space n,
      gaussianFourierKernel n (((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) ξ * φ ξ) atTop
      (𝓝 (∫ ξ : Space n, gaussianFourierKernel n ((b : ℂ)*Complex.I) ξ * φ ξ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (Real.pi/b)^((n : ℝ)/2) * ‖φ ξ‖) _ _ (φ.integrable.norm.const_mul _) _
  · filter_upwards with c
    exact (show Continuous (fun ξ : Space n =>
      gaussianFourierKernel n (((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) ξ * φ ξ) by
        unfold gaussianFourierKernel; fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c hc
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (gaussianFourierKernel_damped_bound hb (inv_nonneg.mpr hc) ξ) (norm_nonneg _)
  · filter_upwards with ξ
    have hh := (gaussianFourierKernel_continuous_damping hn hb ξ).tendsto.comp
      tendsto_inv_atTop_zero
    simpa using hh.mul_const (φ ξ)

theorem gaussian_integral_damping_limit {n : ℕ} {b : ℝ} (φ : 𝓢(Space n, ℂ)) :
    Tendsto (fun c : ℝ => ∫ x : Space n,
      Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x)
      atTop (𝓝 (∫ x : Space n,
        Complex.exp (-((b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖𝓕 φ x‖) _ _ (𝓕 φ).integrable.norm _
  · filter_upwards with c
    exact (show Continuous (fun x : Space n =>
      Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) *
        𝓕 φ x) by fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c hc
    filter_upwards with x
    rw [norm_mul]
    have hh : ‖Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) *
        (‖x‖^2 : ℝ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp only [mul_zero, add_zero, zero_add, sub_zero, mul_one]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (inv_nonneg.mpr hc)) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    have hh := ((tendsto_inv_atTop_zero.ofReal.add_const ((b : ℂ)*Complex.I)).neg.mul_const
      ((‖x‖^2 : ℝ) : ℂ)).cexp
    simpa using hh.mul_const (𝓕 φ x)

theorem gaussian_oscillatory_pairing {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (φ : 𝓢(Space n, ℂ)) :
    (∫ x : Space n, Complex.exp (-((b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x) =
      ∫ ξ : Space n, gaussianFourierKernel n ((b : ℂ)*Complex.I) ξ * φ ξ := by
  have he : (fun c : ℝ => ∫ x : Space n,
      Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x)
      =ᶠ[atTop] (fun c : ℝ => ∫ ξ : Space n,
        gaussianFourierKernel n (((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) ξ * φ ξ) := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact gaussian_fourier_pairing (a := ((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I)
      (by simpa using inv_pos.mpr (show 0 < c from hc)) φ
  exact tendsto_nhds_unique (gaussian_integral_damping_limit φ)
    ((gaussianFourierKernel_integral_limit hn hb φ).congr' he.symm)

theorem gaussian_fresnel_coefficient (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ((Real.pi : ℂ) / ((b : ℂ)*Complex.I))^((n : ℂ)/2) =
      ((Real.pi/b)^((n : ℝ)/2) : ℝ) *
        Complex.exp (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I) := by
  have hr : 0 < Real.pi/b := div_pos Real.pi_pos hb
  have hi : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have he : (Real.pi : ℂ) / ((b : ℂ)*Complex.I) =
      ((Real.pi/b : ℝ) : ℂ)*(-Complex.I) := by
    push_cast
    field_simp
    simp [Complex.I_sq, div_eq_mul_inv]
  rw [he, Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hi),
    Complex.log_ofReal_mul hr hi, Complex.log_neg_I]
  have hex : (((Real.log (Real.pi/b) : ℝ) : ℂ) + (-((Real.pi : ℂ)/2)*Complex.I)) *
        ((n : ℂ)/2) =
      ((Real.log (Real.pi/b) : ℝ) : ℂ)*((n : ℂ)/2) +
        (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I) := by ring
  rw [hex, Complex.exp_add]
  congr 1
  rw [Real.rpow_def_of_pos hr]
  push_cast
  rfl

theorem gaussian_stationary_identity {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (φ : 𝓢(Space n, ℂ)) :
    (∫ x : Space n, Complex.exp (-((b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * φ x) =
      (((Real.pi/b)^((n : ℝ)/2) : ℝ) *
        Complex.exp (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I)) *
      ∫ ξ : Space n, Complex.exp
        (Complex.I*((Real.pi : ℂ)^2*(‖ξ‖^2 : ℝ)/(b : ℂ))) * 𝓕⁻ φ ξ := by
  have hh := gaussian_oscillatory_pairing hn hb (𝓕⁻ φ)
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  rw [hh]
  simp only [gaussianFourierKernel, gaussian_fresnel_coefficient n hb]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  have he : -(Real.pi : ℂ)^2*(‖ξ‖^2 : ℝ)/((b : ℂ)*Complex.I) =
      Complex.I*((Real.pi : ℂ)^2*(‖ξ‖^2 : ℝ)/(b : ℂ)) := by
    field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
    simp [Complex.I_sq]
  rw [he]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuadraticNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact frequency and phase normalization for the negative quadratic form. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem normalized_gaussian_coefficient (n : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    ((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
      (((Real.pi/(Λ/2))^((n : ℝ)/2) : ℝ) *
        Complex.exp (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I)) =
      sphereStationaryConstant n := by
  rw [sphereStationaryConstant, ← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.mul_rpow hΛ.le (by positivity)]
  congr 1
  field_simp [hΛ.ne']

theorem normalized_gaussian_identity {n : ℕ} (hn : 0 < n) {Λ : ℝ} (hΛ : 0 < Λ)
    (φ : 𝓢(Space n, ℂ)) :
    ((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
      (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ)) * φ x) =
      sphereStationaryConstant n * ∫ ξ : Space n,
        PlanarFalconer.imaginaryExponential ((2*Real.pi^2/Λ)*‖ξ‖^2) * 𝓕⁻ φ ξ := by
  have hphase (x : Space n) :
      -(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ) =
        -(((Λ/2 : ℝ) : ℂ)*Complex.I)*(‖x‖^2 : ℝ) := by push_cast; ring
  simp_rw [hphase]
  rw [gaussian_stationary_identity hn (half_pos hΛ), ← mul_assoc,
    normalized_gaussian_coefficient n hΛ]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  congr 1
  unfold PlanarFalconer.imaginaryExponential
  congr 1
  push_cast
  field_simp

theorem norm_sphereStationaryConstant (n : ℕ) :
    ‖sphereStationaryConstant n‖ = (2*Real.pi)^((n : ℝ)/2) := by
  have hp : 0 ≤ (2*Real.pi)^((n : ℝ)/2) := Real.rpow_nonneg (by positivity) _
  simp [sphereStationaryConstant, Complex.norm_real, Complex.norm_exp,
    Complex.mul_re, abs_of_nonneg hp]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_LaplacianFourier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean Laplacian and radial moments of the inverse Fourier transform. -/

namespace Falconer
open MeasureTheory Laplacian
open scoped FourierTransform SchwartzMap LineDeriv RealInnerProductSpace

theorem inverse_fourier_lineDeriv_apply {n : ℕ} (φ : 𝓢(Space n, ℂ))
    (v ξ : Space n) :
    𝓕⁻ (∂_{v} φ) ξ = -(2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℝ) * 𝓕⁻ φ ξ := by
  have hg : (inner ℝ · v).HasTemperateGrowth := by fun_prop
  have h := congrArg (fun f : 𝓢(Space n, ℂ) => f ξ)
    (SchwartzMap.fourierInv_lineDerivOp_eq φ v)
  simpa [SchwartzMap.smulLeftCLM_apply hg, smul_eq_mul, mul_assoc] using h

theorem inverse_fourier_laplacian_apply {n : ℕ} (φ : 𝓢(Space n, ℂ)) (ξ : Space n) :
    𝓕⁻ (Δ φ) ξ = (-(2 * (Real.pi : ℂ))^2 * (‖ξ‖^2 : ℝ)) * 𝓕⁻ φ ξ := by
  let e := stdOrthonormalBasis ℝ (Space n)
  rw [SchwartzMap.laplacian_eq_sum e]
  simp only [FourierTransform.fourierInv_sum, sum_apply, inverse_fourier_lineDeriv_apply]
  have hsum : ∑ i, ((inner ℝ ξ (e i) : ℝ) : ℂ)^2 = (‖ξ‖^2 : ℝ) := by
    exact_mod_cast e.sum_sq_inner_left ξ
  calc
    _ = (-(2 * (Real.pi : ℂ))^2 * ∑ i, ((inner ℝ ξ (e i) : ℝ) : ℂ)^2) *
        𝓕⁻ φ ξ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
      simp [Complex.I_sq]
    _ = _ := by rw [hsum]

theorem schwartz_iterate_laplacian_coe {n : ℕ} (j : ℕ) (φ : 𝓢(Space n, ℂ)) :
    (((laplacian : 𝓢(Space n, ℂ) → 𝓢(Space n, ℂ))^[j] φ) : Space n → ℂ) =
      (laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] (φ : Space n → ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    funext x
    exact SchwartzMap.laplacian_apply _ x

theorem inverse_fourier_iterate_laplacian {n : ℕ} (j : ℕ)
    (φ : 𝓢(Space n, ℂ)) (ξ : Space n) :
    𝓕⁻ ((laplacian : 𝓢(Space n, ℂ) → 𝓢(Space n, ℂ))^[j] φ) ξ =
      (-(2 * (Real.pi : ℂ))^2)^j * ((‖ξ‖^2 : ℝ) : ℂ)^j * 𝓕⁻ φ ξ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', inverse_fourier_laplacian_apply, ih]
    ring

theorem integral_inverse_fourier {n : ℕ} (φ : 𝓢(Space n, ℂ)) :
    (∫ ξ : Space n, 𝓕⁻ φ ξ) = φ 0 := by
  have hid : 𝓕 (𝓕⁻ φ : 𝓢(Space n, ℂ)) = φ := FourierTransform.fourier_fourierInv_eq φ
  have h := congrArg (fun f : 𝓢(Space n, ℂ) => f 0) hid
  change 𝓕 (((𝓕⁻ φ : 𝓢(Space n, ℂ))) : Space n → ℂ) 0 = φ 0 at h
  simpa only [Real.fourier_eq, inner_zero_right, neg_zero,
    AddChar.map_zero_eq_one, one_smul] using h

theorem inverse_fourier_radial_moment {n : ℕ} (j : ℕ) (φ : 𝓢(Space n, ℂ)) :
    (∫ ξ : Space n, ((‖ξ‖^2 : ℝ) : ℂ)^j * 𝓕⁻ φ ξ) =
      ((-(2 * (Real.pi : ℂ))^2)^j)⁻¹ *
        ((laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] (φ : Space n → ℂ)) 0 := by
  have h := integral_inverse_fourier ((laplacian : 𝓢(Space n, ℂ) → 𝓢(Space n, ℂ))^[j] φ)
  simp only [inverse_fourier_iterate_laplacian] at h
  simp_rw [mul_assoc] at h
  rw [integral_const_mul] at h
  rw [← schwartz_iterate_laplacian_coe j φ]
  have hc : (-(2 * (Real.pi : ℂ))^2)^j ≠ 0 := by
    apply pow_ne_zero
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialTaylor
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Taylor expansion in the squared Euclidean radius. -/

namespace Falconer
open MeasureTheory
open PlanarFalconer (imaginaryExponential imaginaryTaylor)
open scoped FourierTransform SchwartzMap

theorem schwartz_radius_power_integrable {n : ℕ} (φ : 𝓢(Space n, ℂ)) (j : ℕ) :
    Integrable (fun x : Space n => ((‖x‖^2 : ℝ) : ℂ)^j * φ x) := by
  apply (φ.integrable_pow_mul volume (2*j)).mono' (by fun_prop)
  filter_upwards with x
  simp [norm_pow, Complex.norm_real, pow_mul]

theorem imaginaryTaylor_radius_integrable {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ) (β : ℝ) :
    Integrable (fun x : Space n => imaginaryTaylor K (β*‖x‖^2) * φ x) := by
  have he : (fun x : Space n => imaginaryTaylor K (β*‖x‖^2)*φ x) =
      fun x => ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          (((‖x‖^2 : ℝ) : ℂ)^j * φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, mul_pow]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j _ => (schwartz_radius_power_integrable φ j).const_mul _)

theorem imaginaryExponential_radius_integrable {n : ℕ} (φ : 𝓢(Space n, ℂ)) (β : ℝ) :
    Integrable (fun x : Space n => imaginaryExponential (β*‖x‖^2) * φ x) := by
  apply φ.integrable.norm.mono' (by unfold imaginaryExponential; fun_prop)
  filter_upwards with x
  have h := PlanarFalconer.imaginaryExponential_derivative_norm 0 (β*‖x‖^2)
  simp only [iteratedDeriv_zero] at h
  rw [norm_mul, h, one_mul]

theorem radial_taylor_integral_bound {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) :
    ‖(∫ x : Space n, imaginaryExponential (β*‖x‖^2)*φ x) -
      (∫ x : Space n, imaginaryTaylor K (β*‖x‖^2)*φ x)‖ ≤
      (β^(K+1)/(K.factorial : ℝ)) *
        ∫ x : Space n, ‖x‖^(2*(K+1))*‖φ x‖ := by
  rw [← integral_sub (imaginaryExponential_radius_integrable φ β)
    (imaginaryTaylor_radius_integrable φ K β), ← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((φ.integrable_pow_mul volume (2*(K+1))).const_mul _) _
  filter_upwards with x
  rw [← sub_mul, norm_mul]
  calc
    _ ≤ ((β*‖x‖^2)^(K+1)/(K.factorial : ℝ))*‖φ x‖ :=
      mul_le_mul_of_nonneg_right (PlanarFalconer.imaginaryExponential_taylor_bound K
        (mul_nonneg hβ (sq_nonneg _))) (norm_nonneg _)
    _ = _ := by rw [mul_pow, pow_mul]; ring

theorem radial_taylor_integral {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ) (β : ℝ) :
    (∫ x : Space n, imaginaryTaylor K (β*‖x‖^2)*φ x) =
      ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          ∫ x : Space n, ((‖x‖^2 : ℝ) : ℂ)^j * φ x := by
  have he : (fun x : Space n => imaginaryTaylor K (β*‖x‖^2)*φ x) =
      fun x => ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          (((‖x‖^2 : ℝ) : ℂ)^j * φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, mul_pow]
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_const_mul _ _
  · intro j _
    exact (schwartz_radius_power_integrable φ j).const_mul _

theorem radial_taylor_inverse_integral {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ) (β : ℝ) :
    (∫ x : Space n, imaginaryTaylor K (β*‖x‖^2)*𝓕⁻ φ x) =
      ∑ j ∈ Finset.range (K+1),
        (((j.factorial : ℝ)⁻¹ * β^j : ℝ) : ℂ) * Complex.I^j *
          (((-(2 * (Real.pi : ℂ))^2)^j)⁻¹ *
            ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
              (φ : Space n → ℂ)) 0) := by
  rw [radial_taylor_integral]
  simp only [inverse_fourier_radial_moment]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticCoefficients
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the Fourier Taylor coefficients with the actual Laplacian jets. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem quadratic_taylor_scalar (j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    (((j.factorial : ℝ)⁻¹ * (2*Real.pi^2/Λ)^j : ℝ) : ℂ) * Complex.I^j *
      ((-(2 * (Real.pi : ℂ))^2)^j)⁻¹ =
        ((Λ^(-(j : ℝ)) : ℝ) : ℂ) / ((2*Complex.I)^j * (j.factorial : ℂ)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hl : (Λ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΛ.ne'
  have hbase : (2*(Real.pi : ℂ)^2/(Λ : ℂ)) * Complex.I *
      (-(2*(Real.pi : ℂ))^2)⁻¹ = (Λ : ℂ)⁻¹ * (2*Complex.I)⁻¹ := by
    field_simp [hp, hl]
    simp [Complex.I_sq]
  rw [Real.rpow_neg hΛ.le, Real.rpow_natCast]
  push_cast
  calc
    _ = (j.factorial : ℂ)⁻¹ *
        ((2*(Real.pi : ℂ)^2/(Λ : ℂ))*Complex.I*(-(2*(Real.pi : ℂ))^2)⁻¹)^j := by
      rw [mul_pow, mul_pow, inv_pow]
      ring
    _ = _ := by
      rw [hbase]
      simp only [mul_pow, inv_pow, div_eq_mul_inv]
      ring

theorem normalized_quadratic_taylor {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    sphereStationaryConstant n *
      (∫ x : Space n, PlanarFalconer.imaginaryTaylor K ((2*Real.pi^2/Λ)*‖x‖^2)*𝓕⁻ φ x) =
      ∑ j ∈ Finset.range (K+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j φ := by
  rw [radial_taylor_inverse_integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold quadraticJetCoefficient
  have h := quadratic_taylor_scalar j hΛ
  calc
    _ = sphereStationaryConstant n *
        ((((j.factorial : ℝ)⁻¹ * (2*Real.pi^2/Λ)^j : ℝ) : ℂ) * Complex.I^j *
          ((-(2*(Real.pi : ℂ))^2)^j)⁻¹) *
          ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
            (φ : Space n → ℂ)) 0 := by ring
    _ = _ := by rw [h]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CompactFourierBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-support Fourier moment bounds with a total derivative budget. -/

namespace Falconer
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

theorem integral_compact_derivative_bound {n : ℕ} (φ : 𝓢(Space n, ℂ))
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Space n) 1)
    (k : ℕ) {B : ℝ}
    (hd : ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ B) :
    (∫ x : Space n, ‖iteratedFDeriv ℝ k φ x‖) ≤ unitBallVolume n * B := by
  have hi : Integrable (fun x : Space n => ‖iteratedFDeriv ℝ k φ x‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 k
  have he : (∫ x in Metric.closedBall (0 : Space n) 1, ‖iteratedFDeriv ℝ k φ x‖) =
      ∫ x : Space n, ‖iteratedFDeriv ℝ k φ x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ∉ Function.support (iteratedFDeriv ℝ k (φ : Space n → ℂ)) :=
      fun h => hx (hs ((support_iteratedFDeriv_subset k) h))
    simpa only [Function.mem_support, not_not, norm_eq_zero] using hx'
  rw [← he]
  calc
    _ ≤ ∫ _x in Metric.closedBall (0 : Space n) 1, B :=
      integral_mono hi.integrableOn (integrableOn_const measure_closedBall_lt_top.ne) hd
    _ = _ := by simp [unitBallVolume, measureReal_def]

theorem compact_fourier_decay {n m : ℕ} (φ : 𝓢(Space n, ℂ))
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Space n) 1)
    {B : ℝ} (_hB : 0 ≤ B)
    (hd : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ B) (ξ : Space n) :
    ‖ξ‖^m * ‖𝓕 φ ξ‖ ≤ (2 : ℝ)^m * (m+1) * unitBallVolume n * B := by
  have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (φ.smooth ⊤)
    (fun k j _ _ => φ.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := m) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ξ
  have hsum : (∑ p ∈ Finset.range (0+1) ×ˢ Finset.range (m+1),
      ∫ x : Space n, ‖x‖^p.1 * ‖iteratedFDeriv ℝ p.2 φ x‖) ≤
      (m+1) * (unitBallVolume n * B) := by
    calc
      _ ≤ ∑ _p ∈ Finset.range (0+1) ×ˢ Finset.range (m+1), unitBallVolume n * B := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hp0 : p.1 = 0 := by simpa using hp'.1
        have hp2 : p.2 ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hp'.2)
        simpa [hp0] using integral_compact_derivative_bound φ hs p.2 (hd p.2 hp2)
      _ = _ := by simp
  calc
    _ ≤ (2 : ℝ)^m * _ := by simpa [SchwartzMap.fourier_coe] using hh
    _ ≤ (2 : ℝ)^m * ((m+1) * (unitBallVolume n * B)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem compact_inverse_fourier_decay {n m : ℕ} (φ : 𝓢(Space n, ℂ))
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Space n) 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ B) (ξ : Space n) :
    ‖ξ‖^m * ‖𝓕⁻ φ ξ‖ ≤ (2 : ℝ)^m * (m+1) * unitBallVolume n * B := by
  have h := compact_fourier_decay φ hs hB hd (-ξ)
  simpa [SchwartzMap.fourierInv_apply_eq] using h

theorem compact_inverse_fourier_moment_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space n, ℂ)),
      tsupport φ ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ k+n+1, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ B) →
      (∫ ξ : Space n, ‖ξ‖^k * ‖𝓕⁻ φ ξ‖) ≤ C * B := by
  let q := n+1
  let A := (2 : ℝ)^(k+q) * ((k+q : ℕ)+1) * unitBallVolume n
  let W := ∫ x : Space n, (1+‖x‖)^(-(q : ℝ))
  refine ⟨2^q * W * (unitBallVolume n + A), by
    dsimp [W, A, unitBallVolume]
    positivity, ?_⟩
  intro φ hs B hB hd
  have h0 (ξ : Space n) : ‖𝓕⁻ φ ξ‖ ≤ unitBallVolume n * B := by
    have h := compact_inverse_fourier_decay (m := 0) φ hs hB
      (fun j hj => hd j (by omega)) ξ
    simpa using h
  have htop (ξ : Space n) : ‖ξ‖^(k+q) * ‖𝓕⁻ φ ξ‖ ≤ A * B := by
    exact compact_inverse_fourier_decay φ hs hB (fun j hj => hd j (by dsimp [q] at hj; omega)) ξ
  have hW : Integrable (fun x : Space n => (1+‖x‖)^(-(q : ℝ))) := by
    apply integrable_one_add_norm
    simp [Space, q]
  calc
    _ ≤ ∫ ξ : Space n, (2^q * (unitBallVolume n * B + A * B)) *
        (1+‖ξ‖)^(-(q : ℝ)) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ξ => by positivity) (hW.const_mul _)
      filter_upwards with ξ
      exact pow_mul_le_of_le_of_pow_mul_le (norm_nonneg ξ) (norm_nonneg _) (h0 ξ) (htop ξ)
    _ = _ := by rw [integral_const_mul]; dsimp [W]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticDischarge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of the fixed negative-quadratic stationary-phase input. -/

namespace Falconer
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

theorem quadratic_stationary_schwartz (n K : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space n, ℂ)),
      tsupport φ ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ 2*(K+1)+n+1, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ B) →
      ∀ Λ : ℝ, 1 ≤ Λ →
        ‖((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
          (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ)) * φ x) -
          ∑ j ∈ Finset.range (K+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j φ‖ ≤
            C * Λ^(-((K+1 : ℕ) : ℝ)) * B := by
  obtain ⟨M, hM, hm⟩ := compact_inverse_fourier_moment_bound n (2*(K+1))
  let A := (2*Real.pi)^((n : ℝ)/2)
  let D := (2*Real.pi^2)^(K+1)/(K.factorial : ℝ)
  refine ⟨A*D*M, by dsimp [A, D]; positivity, ?_⟩
  intro φ hs B hB hd Λ hΛ
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hβ : 0 ≤ 2*Real.pi^2/Λ := by positivity
  have hmoment := hm φ hs B hB hd
  have ht := radial_taylor_integral_bound (𝓕⁻ φ) K hβ
  have he : ‖((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
        (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ)) * φ x) -
        ∑ j ∈ Finset.range (K+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j φ‖ =
      A * ‖(∫ x : Space n, PlanarFalconer.imaginaryExponential
          ((2*Real.pi^2/Λ)*‖x‖^2)*𝓕⁻ φ x) -
        (∫ x : Space n, PlanarFalconer.imaginaryTaylor K
          ((2*Real.pi^2/Λ)*‖x‖^2)*𝓕⁻ φ x)‖ := by
    rw [normalized_gaussian_identity hn hΛ0 φ, ← normalized_quadratic_taylor φ K hΛ0,
      ← mul_sub, norm_mul, norm_sphereStationaryConstant]
  rw [he]
  calc
    _ ≤ A * (((2*Real.pi^2/Λ)^(K+1)/(K.factorial : ℝ)) *
        ∫ x : Space n, ‖x‖^(2*(K+1))*‖𝓕⁻ φ x‖) :=
      mul_le_mul_of_nonneg_left ht (by dsimp [A]; positivity)
    _ ≤ A * (((2*Real.pi^2/Λ)^(K+1)/(K.factorial : ℝ)) * (M*B)) := by
      gcongr
    _ = (A*D*M) * Λ^(-((K+1 : ℕ) : ℝ)) * B := by
      rw [Real.rpow_neg hΛ0.le, Real.rpow_natCast, div_pow]
      dsimp [D]
      ring

theorem published_quadratic_stationary : PublishedQuadraticStationary := by
  intro n J hn hJ
  cases J with
  | zero => omega
  | succ K =>
    obtain ⟨C, hC, hc⟩ := quadratic_stationary_schwartz n K (by omega)
    refine ⟨C, hC, ?_⟩
    intro a ha hs B hB hd Λ hΛ
    have hsupp : HasCompactSupport a :=
      (isCompact_closedBall (0 : Space n) 1).of_isClosed_subset isClosed_closure hs
    let φ : 𝓢(Space n, ℂ) := hsupp.toSchwartzMap ha
    exact hc φ hs B hB hd Λ hΛ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMoments
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From radial projection moments to integer cap availability

The radial pushforwards form a Markov kernel. Mathlib's kernel
Radon--Nikodym derivative supplies a jointly measurable version of all
their angular densities, so separate choices of densities are unnecessary.
This connects the published radial-moment input to the truncation step.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The moment written as an integral of the density agrees with the
published convention of taking the `p`th power of its `Lᵖ` norm. -/
theorem radial_rnDeriv_moment_eq_norm {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ a, ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ) =
      (eLpNorm (fun a => (((ν : Measure (Space d)).map
        (radialDirection x)).rnDeriv σ a).toReal) (ENNReal.ofReal p) σ) ^ p := by
  let γ := (ν : Measure (Space d)).map (radialDirection x)
  have hγ : IsFiniteMeasure γ := by
    dsimp [γ]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (γ.rnDeriv σ) := Measure.measurable_rnDeriv γ σ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top γ σ] with a ha
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal ha.ne]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMomentParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exponents used in Orponen's published radial moment estimate -/

namespace Falconer

theorem radial_moment_parameters {h δ : ℝ} (hh : 1 ≤ h) (hδ : 0 < δ) (hδ1 : δ < 1) :
    h < h+δ/2 ∧ h+δ/2 < h+1 ∧ 0 < h-δ/4 ∧ h-δ/4 < h ∧
    2*h-(h+δ/2) < h-δ/4 ∧ 1 < 1+δ/(8*h) ∧
    1+δ/(8*h) < 2-(h-δ/4)/h ∧
    1+δ/(8*h) < (h-δ/4)/(2*h-(h+δ/2)) := by
  have hh0 : 0 < h := by linarith only [hh]
  have hden : 0 < 2*h-(h+δ/2) := by linarith only [hh,hδ1]
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_,?_,?_⟩
  · have := div_pos hδ (mul_pos (by norm_num : (0:ℝ) < 8) hh0)
    linarith
  · have he : 2-(h-δ/4)/h = 1+δ/(4*h) := by
      field_simp
      ring
    rw [he]
    have hd := div_lt_div_of_pos_left hδ
      (by positivity : 0 < 4*h) (by linarith : 4*h < 8*h)
    linarith only [hd]
  · apply (lt_div_iff₀ hden).mpr
    have he : (1+δ/(8*h))*(2*h-(h+δ/2)) = h-3*δ/8-δ^2/(16*h) := by
      field_simp
      ring
    rw [he]
    have hn : 0 ≤ δ^2/(16*h) := by positivity
    linarith only [hδ,hn]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SimilarityMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original measure and radial-cap transport under a common similarity -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

@[simp] theorem pairHomeomorph_mem_image (f : Space d ≃ₜ Space d)
    (G : Set (Space d × Space d)) (x y : Space d) :
    (f x,f y) ∈ pairHomeomorph f '' G ↔ (x,y) ∈ G :=
  (pairHomeomorph f).injective.mem_set_image (s := G) (a := (x,y))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TwoInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer

theorem mainTarget_of_two_published_inputs
    (hRadial : PublishedRadialMoment)
    (hFurstenberg : PublishedPlanarFurstenberg) : MainTarget :=
  mainTarget_of_three_published_inputs hRadial hFurstenberg published_quadratic_stationary

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SurfaceTestNorm
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous test norms against the actual ambient surface measure.
These measure-duality lemmas match the published radial pushforward directly. -/

namespace Falconer
open Set MeasureTheory Filter PlanarFalconer
open scoped ENNReal NNReal Topology
variable {d : ℕ}


theorem surfaceTestNorm_test_bound (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {q : ℝ} (hN : surfaceTestNorm q γ ≠ ∞)
    (F : BoundedContinuousFunction (Space (d+1)) ℝ) :
    ‖∫ ω, F ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal *
      (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal := by
  have hf : MemLp F (ENNReal.ofReal q) (surfaceMeasure (d+1)) :=
    (memLp_top_of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Eventually.of_forall F.norm_coe_le_norm)).mono_exponent le_top
  have haux (a : ℝ) (ha : (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal < a) :
      ‖∫ ω, F ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal * a := by
    have ha0 : 0 < a := lt_of_le_of_lt ENNReal.toReal_nonneg ha
    let G : BoundedContinuousFunction (Space (d+1)) ℝ := a⁻¹ • F
    have hG : eLpNorm G (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1 := by
      change eLpNorm (a⁻¹ • (F : (Space (d+1)) → ℝ)) _ _ ≤ _
      rw [eLpNorm_const_smul]
      have hn : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ ENNReal.ofReal a :=
        (ENNReal.le_ofReal_iff_toReal_le hf.eLpNorm_ne_top ha0.le).mpr ha.le
      calc
        ‖a⁻¹‖ₑ * eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤
            ENNReal.ofReal a⁻¹ * ENNReal.ofReal a := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
          exact mul_le_mul_right hn _
        _ = 1 := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha0.le), inv_mul_cancel₀ ha0.ne', ENNReal.ofReal_one]
    have hb : ENNReal.ofReal ‖∫ ω, G ω ∂γ‖ ≤ surfaceTestNorm q γ :=
      le_iSup_of_le G (le_iSup_of_le hG le_rfl)
    have hb' := (ENNReal.ofReal_le_iff_le_toReal hN).mp hb
    change ‖∫ ω, a⁻¹ • F ω ∂γ‖ ≤ _ at hb'
    rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)] at hb'
    calc
      ‖∫ ω, F ω ∂γ‖ = a * (a⁻¹ * ‖∫ ω, F ω ∂γ‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
      _ ≤ a * (surfaceTestNorm q γ).toReal := mul_le_mul_of_nonneg_left hb' ha0.le
      _ = _ := mul_comm _ _
  apply ge_of_tendsto (f := fun a : ℝ => (surfaceTestNorm q γ).toReal * a)
    ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left
      (show 𝓝[>] (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal ≤
        𝓝 (eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact haux a ha



theorem surfaceTestNorm_measurable_test_bound (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : surfaceTestNorm q γ ≠ ∞)
    (f : (Space (d+1)) → ℝ) (hf : MemLp f (ENNReal.ofReal q) (γ + (surfaceMeasure (d+1)))) :
    ‖∫ ω, f ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal *
      (eLpNorm f (ENNReal.ofReal q) (surfaceMeasure (d+1))).toReal := by
  let μ := γ + (surfaceMeasure (d+1))
  let Q := ENNReal.ofReal q
  have hQ : 1 ≤ Q := by simpa [Q] using ENNReal.ofReal_le_ofReal hq
  let : Fact (1 ≤ Q) := ⟨hQ⟩
  have hγ : γ ≤ μ := le_add_of_nonneg_right bot_le
  have hν : (surfaceMeasure (d+1)) ≤ μ := le_add_of_nonneg_left bot_le
  have hν' : (surfaceMeasure (d+1)) ≤ (1 : ℝ≥0∞) • μ := by simpa using hν
  let R : Lp ℝ Q μ →L[ℝ] Lp ℝ Q (surfaceMeasure (d+1)) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν'
  have hR (g : Lp ℝ Q μ) : R g =ᵐ[(surfaceMeasure (d+1))] g :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν' g
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (show Q ≠ ∞ from ENNReal.ofReal_ne_top)
  have hclosed : IsClosed {g : Lp ℝ Q μ | ‖∫ ω, g ω ∂γ‖ ≤
      (surfaceTestNorm q γ).toReal * ‖R g‖} :=
    isClosed_le (continuous_integral_Lp_of_le γ μ hγ hQ).norm
      (continuous_const.mul R.continuous.norm)
  have hall (g : Lp ℝ Q μ) : ‖∫ ω, g ω ∂γ‖ ≤ (surfaceTestNorm q γ).toReal * ‖R g‖ := by
    apply (hclosed.closure_subset_iff (s := Set.range (BoundedContinuousFunction.toLp Q μ ℝ))).mpr ?_ (hd g)
    rintro _ ⟨F, rfl⟩
    have hF := BoundedContinuousFunction.coeFn_toLp Q μ ℝ F
    have hi := integral_congr_ae (hγ.absolutelyContinuous.ae_eq hF)
    have hn : ‖R (BoundedContinuousFunction.toLp Q μ ℝ F)‖ =
        (eLpNorm F Q (surfaceMeasure (d+1))).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq hF))]
    change ‖∫ ω, (BoundedContinuousFunction.toLp Q μ ℝ F) ω ∂γ‖ ≤ _
    rw [hi, hn]
    exact surfaceTestNorm_test_bound γ hN F
  have hg := hall (hf.toLp f)
  have he := hf.coeFn_toLp
  rw [integral_congr_ae (hγ.absolutelyContinuous.ae_eq he)] at hg
  have hn : ‖R (hf.toLp f)‖ = (eLpNorm f Q (surfaceMeasure (d+1))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq he))]
  rwa [hn] at hg

theorem surfaceTestNorm_absolutelyContinuous (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : surfaceTestNorm q γ ≠ ∞) : γ ≪ (surfaceMeasure (d+1)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  let f : (Space (d+1)) → ℝ := s.indicator (fun _ => 1)
  have hf : MemLp f (ENNReal.ofReal q) (γ + (surfaceMeasure (d+1))) :=
    memLp_indicator_const _ hs _ (Or.inr (measure_ne_top _ _))
  have hb := surfaceTestNorm_measurable_test_bound γ hq hN f hf
  have he : f =ᵐ[(surfaceMeasure (d+1))] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνs] with x hx
    exact Set.indicator_of_notMem hx _
  rw [eLpNorm_congr_ae he, eLpNorm_zero, ENNReal.toReal_zero, mul_zero] at hb
  have hi : (∫ x, f x ∂γ) = (γ s).toReal := by
    simp [f, integral_indicator hs, measureReal_def]
  rw [hi, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hb
  exact ((ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hb ENNReal.toReal_nonneg)).resolve_right
    (measure_ne_top γ s)



theorem surfaceTestNorm_bounded_density_lower (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : surfaceTestNorm q γ ≠ ∞)
    (F : (Space (d+1)) → ℝ≥0∞) (hF : Measurable F) {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hFB : ∀ x, F x ≤ B)
    (hFR : ∀ᵐ x ∂(surfaceMeasure (d+1)), F x ≤ γ.rnDeriv (surfaceMeasure (d+1)) x) :
    (∫⁻ x, F x^p ∂(surfaceMeasure (d+1)))^(1/p) ≤ surfaceTestNorm q γ := by
  let : γ.HaveLebesgueDecomposition (surfaceMeasure (d+1)) :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hq : 1 ≤ q := (Real.holderConjugate_iff.mp hpq.symm).1.le
  have hAC := surfaceTestNorm_absolutelyContinuous γ hq hN
  have hmass : (∫⁻ x, F x^p ∂(surfaceMeasure (d+1))) ≠ ∞ := by
    apply ne_of_lt
    calc
      (∫⁻ x, F x^p ∂(surfaceMeasure (d+1))) ≤ ∫⁻ _, B^p ∂(surfaceMeasure (d+1)) :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hFB x) hpq.nonneg)
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg hB).lt_top
          (measure_lt_top (surfaceMeasure (d+1)) univ)
  by_cases hzero : (∫⁻ x, F x^p ∂(surfaceMeasure (d+1))) = 0
  · rw [hzero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos)]
    exact bot_le
  obtain ⟨h, hh, ⟨C, hC, hhC⟩, hnorm, hpair⟩ :=
    exists_bounded_normalized_dual_density (surfaceMeasure (d+1)) F hF hpq hB hFB hzero hmass
  have hht (x : (Space (d+1))) : h x ≠ ∞ := ne_of_lt ((hhC x).trans_lt hC.lt_top)
  have hen (x : (Space (d+1))) : ‖(h x).toReal‖ₑ = h x := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hht x)]
  have hm : MemLp (fun x => (h x).toReal) (ENNReal.ofReal q) (γ + (surfaceMeasure (d+1))) :=
    (memLp_top_of_bound hh.ennreal_toReal.aestronglyMeasurable C.toReal
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono hC (hhC x)))).mono_exponent le_top
  have hn : eLpNorm (fun x => (h x).toReal) (ENNReal.ofReal q) (surfaceMeasure (d+1)) = 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.symm.nonneg]
    simp_rw [hen]
    rw [hnorm, ENNReal.one_rpow]
  have hb := surfaceTestNorm_measurable_test_bound γ hq hN (fun x => (h x).toReal) hm
  rw [hn, ENNReal.toReal_one, mul_one] at hb
  have hi : Integrable (fun x => (h x).toReal) γ :=
    (hm.mono_measure (le_add_of_nonneg_right bot_le)).integrable
      (by simpa using ENNReal.ofReal_le_ofReal hq)
  have hlin : (∫⁻ x, h x ∂γ) ≤ surfaceTestNorm q γ := by
    have he : ENNReal.ofReal ‖∫ x, (h x).toReal ∂γ‖ = ∫⁻ x, h x ∂γ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => ENNReal.toReal_nonneg)),
        ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
      exact lintegral_congr (fun x => ENNReal.ofReal_toReal (hht x))
    rw [← he]
    exact (ENNReal.ofReal_le_iff_le_toReal hN).mpr hb
  rw [← hpair]
  calc
    (∫⁻ x, F x * h x ∂(surfaceMeasure (d+1))) ≤
        ∫⁻ x, γ.rnDeriv (surfaceMeasure (d+1)) x * h x ∂(surfaceMeasure (d+1)) :=
      lintegral_mono_ae (hFR.mono (fun x hx => mul_le_mul_left hx _))
    _ = ∫⁻ x, h x ∂γ := by
      have he := lintegral_withDensity_eq_lintegral_mul (surfaceMeasure (d+1))
        (Measure.measurable_rnDeriv γ (surfaceMeasure (d+1))) hh
      rw [Measure.withDensity_rnDeriv_eq γ (surfaceMeasure (d+1)) hAC] at he
      exact he.symm
    _ ≤ _ := hlin



theorem surfaceTestNorm_rnDeriv_eLpNorm_le (γ : Measure (Space (d+1))) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : surfaceTestNorm q γ ≠ ∞) :
    eLpNorm (fun x => (γ.rnDeriv (surfaceMeasure (d+1)) x).toReal) (ENNReal.ofReal p) (surfaceMeasure (d+1)) ≤
      surfaceTestNorm q γ := by
  let R := γ.rnDeriv (surfaceMeasure (d+1))
  let F : ℕ → (Space (d+1)) → ℝ := fun n x => min (R x).toReal n
  have hm (n : ℕ) : Measurable (F n) :=
    (Measure.measurable_rnDeriv γ (surfaceMeasure (d+1))).ennreal_toReal.min measurable_const
  have hpos (n : ℕ) (x : (Space (d+1))) : 0 ≤ F n x :=
    le_min ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hb (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) (surfaceMeasure (d+1)) ≤ surfaceTestNorm q γ := by
    have h := surfaceTestNorm_bounded_density_lower γ hpq hN
      (fun x => ENNReal.ofReal (F n x)) (hm n).ennreal_ofReal ENNReal.ofReal_ne_top
      (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      (Eventually.of_forall (fun x =>
        (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (ENNReal.ofReal_toReal_le)))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.nonneg]
    simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hpos n _)] using h
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hb)
    (fun index => (hm index).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (R x).toReal
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (min_eq_left (hn.trans (by exact_mod_cast hm))).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialAtomless
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the radial test norm from finite positive Riesz energy. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem nullSingletonClass_of_finite_rieszEnergy {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] {s : ℝ} (hs : 0 < s) (hμ : PlanarFalconer.rieszEnergyOn μ s < ∞) :
    NullSingletonClass μ := by
  have hf := ae_lt_top (μ := μ.prod μ)
    (show Measurable (fun z : Space d × Space d => (edist z.1 z.2)^(-s)) by fun_prop) hμ.ne
  have hneq : ∀ᵐ z : Space d × Space d ∂μ.prod μ, z.1 ≠ z.2 := by
    filter_upwards [hf] with z hz he
    simp only [he, edist_self, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hs), lt_self_iff_false] at hz
  have hdiag : μ.prod μ {z : Space d × Space d | z.1 = z.2} = 0 := by
    simpa only [ae_iff, not_not] using hneq
  constructor
  intro x
  have hsub : ({x} : Set (Space d)) ×ˢ {x} ⊆ {z : Space d × Space d | z.1 = z.2} := by
    rintro ⟨y,z⟩ ⟨hy,hz⟩
    exact hy.trans hz.symm
  have h := measure_mono_null hsub hdiag
  rw [Measure.prod_prod] at h
  exact (mul_eq_zero.mp h).elim id id

theorem continuousAt_radialDirection_center {d : ℕ} (x y : Space d) (hy : y ≠ x) :
    ContinuousAt (fun z => radialDirection z y) x := by
  have hd : ContinuousAt (fun z : Space d => y-z) x :=
    (continuous_const.sub continuous_id).continuousAt
  exact (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd

theorem continuous_atomless_radial_ambient_test {d : ℕ} (α : Measure (Space d))
    [IsFiniteMeasure α] [NullSingletonClass α] (F : BoundedContinuousFunction (Space d) ℝ) :
    Continuous (fun x => ∫ w, F w ∂α.map (radialDirection x)) := by
  have hm (x : Space d) : Measurable (radialDirection x) := by unfold radialDirection; fun_prop
  simp_rw [integral_map (hm _).aemeasurable F.continuous.aestronglyMeasurable]
  rw [continuous_iff_continuousAt]
  intro x
  apply continuousAt_of_dominated (bound := fun _ : Space d => ‖F‖)
  · exact Eventually.of_forall (fun z => (F.continuous.measurable.comp (hm z)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => F.norm_coe_le_norm _))
  · exact integrable_const _
  · filter_upwards [(show ∀ᵐ y ∂α, y ≠ x from by rw [ae_iff]; simp)] with y hy
    exact F.continuous.continuousAt.comp (continuousAt_radialDirection_center x y hy)

theorem surfaceTestNorm_atomless_radial_measurable {n : ℕ} (α : Measure (Space (n+1)))
    [IsFiniteMeasure α] [NullSingletonClass α] (q : ℝ) :
    Measurable (fun x => surfaceTestNorm q (α.map (radialDirection x))) := by
  apply LowerSemicontinuous.measurable
  unfold surfaceTestNorm
  apply lowerSemicontinuous_biSup
  intro F _
  exact (ENNReal.continuous_ofReal.comp (continuous_atomless_radial_ambient_test α F).norm).lowerSemicontinuous

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialDischarge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent proof of the precise published radial input, using the actual
Euclidean surface measure, orthogonal slices, and smooth approximation. -/
namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

theorem finite_euclidean_radial_moment (n : ℕ)
    (α : ProbabilityMeasure (Space (n+1))) (β : Measure (Space (n+1))) [IsFiniteMeasure β]
    {K L : Set (Space (n+1))} (hK : IsCompact K) (hL : IsCompact L)
    (hα : ∀ᵐ z ∂(α : Measure (Space (n+1))), z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L)
    {s t p q : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n)
    (hEα : rieszEnergyOn (α : Measure (Space (n+1))) s < ∞)
    (hEβ : rieszEnergyOn β t < ∞) :
    (∀ᵐ x ∂β, (α : Measure (Space (n+1))).map (radialDirection x) ≪ surfaceMeasure (n+1)) ∧
    (∫⁻ x, ∫⁻ w, ((α : Measure (Space (n+1))).map (radialDirection x)).rnDeriv
      (surfaceMeasure (n+1)) w ^ p ∂surfaceMeasure (n+1) ∂β) < ∞ := by
  let := nullSingletonClass_of_finite_rieszEnergy (α : Measure (Space (n+1))) hs0 hEα
  have hf := finite_euclidean_radial_testNorm_moment n (α : Measure (Space (n+1))) β
    hK hL hα hβ hs0 hs hsn hs2 ht hpq hp2 hupt htr hEα hEβ
  have hm := (surfaceTestNorm_atomless_radial_measurable (α : Measure (Space (n+1))) q).pow_const p
  have ha := ae_lt_top hm hf.ne
  have hN : ∀ᵐ x ∂β, surfaceTestNorm q ((α : Measure (Space (n+1))).map (radialDirection x)) ≠ ∞ := by
    filter_upwards [ha] with x hx he
    simp only [he, ENNReal.top_rpow_of_pos hpq.pos, lt_self_iff_false] at hx
  refine ⟨hN.mono (fun x hx => surfaceTestNorm_absolutelyContinuous _
    (Real.holderConjugate_iff.mp hpq.symm).1.le hx), ?_⟩
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) hf
  filter_upwards [hN] with x hx
  rw [radial_rnDeriv_moment_eq_norm α (surfaceMeasure (n+1)) x hpq.pos]
  exact ENNReal.rpow_le_rpow (surfaceTestNorm_rnDeriv_eLpNorm_le _ hpq hx) hpq.nonneg

theorem published_radial_moment : PublishedRadialMoment := by
  intro n hn α β δ hδ hδ1 hα hβ _hsep hEα hEβ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hs,hsn,ht,_htn,_hut,hp,hpt,hps⟩ := radial_moment_parameters hn1 hδ hδ1
  have hu0 : 0 < 2*(n : ℝ)-((n : ℝ)+δ/2) := by linarith
  have hs0 : 0 < (n : ℝ)+δ/2 := by linarith
  have hs2 : (n : ℝ)+δ/2 < 2*n := by linarith
  have hp2 : 1+δ/(8*(n : ℝ)) < 2 :=
    hpt.trans_le (sub_le_self _ (div_nonneg ht.le hn0.le))
  have hupt : (2*(n : ℝ)-((n : ℝ)+δ/2))*(1+δ/(8*(n : ℝ))) < (n : ℝ)-δ/4 :=
    by simpa only [mul_comm] using (lt_div_iff₀ hu0).mp hps
  have htr : ((n : ℝ)-δ/4)/(2-(1+δ/(8*(n : ℝ)))) < n := by
    apply (div_lt_iff₀ (by linarith)).mpr
    have hh := mul_lt_mul_of_pos_right hpt hn0
    have he : (((n : ℝ)-δ/4)/(n : ℝ))*(n : ℝ) = (n : ℝ)-δ/4 :=
      div_mul_cancel₀ _ hn0.ne'
    nlinarith
  have hpq : (1+δ/(8*(n : ℝ))).HolderConjugate
      ((1+δ/(8*(n : ℝ)))/((1+δ/(8*(n : ℝ)))-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  exact finite_euclidean_radial_moment n α (β : Measure (Space (n+1))) hα hβ
    (α : Measure (Space (n+1))).support_mem_ae (β : Measure (Space (n+1))).support_mem_ae
    hs0 hs hsn hs2 ht hpq hp2 hupt htr hEα hEβ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OneInputMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer

/-- Exact all-dimensional conclusion after independently proving the radial input. -/
theorem mainTarget_of_planar_furstenberg
    (hFurstenberg : PublishedPlanarFurstenberg) : MainTarget :=
  mainTarget_of_two_published_inputs published_radial_moment hFurstenberg

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Campaign123PlanarFurstenbergProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the precise planar Furstenberg specialization used by the
all-dimensional Falconer proof, by the finite multiscale incidence argument. -/
namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem falconer_distance_conjecture_oai :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
      (d : ℝ≥0∞) / 2 < dimH E →
        0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} :=
  mainTarget_of_planar_furstenberg publishedPlanarFurstenberg_proved

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.falconer_distance_conjecture_oai := @OAI.Falconer.falconer_distance_conjecture_oai
