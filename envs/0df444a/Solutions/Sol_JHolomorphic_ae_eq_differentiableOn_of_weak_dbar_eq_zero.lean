-- Prove2me | solution 1 for JHolomorphic.ae_eq_differentiableOn_of_weak_dbar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:18:19.114002+00:00
-- url     : https://prove2.me/submissions/9cae5a19-85b7-4b9d-a1ed-f05089ee5bc5

import Mathlib
import Definitions.Def_JHolomorphic_Setting

set_option linter.all false

namespace WeylDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal Real

noncomputable section

/-- unnormalized radial bump -/
def ρ0 (w : ℂ) : ℝ := Real.smoothTransition (1 - ‖w‖ ^ 2)

lemma ρ0_contDiff : ContDiff ℝ ∞ ρ0 := by
  unfold ρ0
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma ρ0_nonneg (w : ℂ) : 0 ≤ ρ0 w := Real.smoothTransition.nonneg _

lemma ρ0_le_one (w : ℂ) : ρ0 w ≤ 1 := Real.smoothTransition.le_one _

lemma ρ0_eq_zero {w : ℂ} (hw : 1 ≤ ‖w‖) : ρ0 w = 0 := by
  unfold ρ0
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg w]

lemma ρ0_support : Function.support ρ0 ⊆ ball 0 1 := by
  intro w hw
  by_contra h
  simp only [mem_ball, dist_zero_right, not_lt] at h
  exact hw (ρ0_eq_zero h)

lemma ρ0_hasCompactSupport : HasCompactSupport ρ0 :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1)
    (ρ0_support.trans ball_subset_closedBall)

lemma c0_pos : 0 < ∫ w, ρ0 w := by
  apply ρ0_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ρ0_hasCompactSupport ρ0_nonneg (x := 0)
  simp [ρ0, Real.smoothTransition.one_of_one_le]

def c0 : ℝ := ∫ w, ρ0 w

/-- normalized radial mollifier of radius `ε` -/
def ρ (ε : ℝ) (w : ℂ) : ℝ := ρ0 (ε⁻¹ • w) / (ε ^ 2 * c0)

lemma ρ_contDiff (ε : ℝ) : ContDiff ℝ ∞ (ρ ε) := by
  unfold ρ
  exact (ρ0_contDiff.comp (contDiff_const_smul _)).div_const _

lemma ρ_nonneg {ε : ℝ} (w : ℂ) : 0 ≤ ρ ε w :=
  div_nonneg (ρ0_nonneg _) (mul_nonneg (sq_nonneg _) c0_pos.le)

lemma ρ_eq_zero {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : ε ≤ ‖w‖) : ρ ε w = 0 := by
  unfold ρ
  rw [ρ0_eq_zero, zero_div]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  rw [le_inv_mul_iff₀ hε]; simpa using hw

lemma ρ_support {ε : ℝ} (hε : 0 < ε) : Function.support (ρ ε) ⊆ ball 0 ε := by
  intro w hw
  by_contra h
  simp only [mem_ball, dist_zero_right, not_lt] at h
  exact hw (ρ_eq_zero hε h)

lemma ρ_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ρ ε) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ε)
    ((ρ_support hε).trans ball_subset_closedBall)

lemma ρ_le {ε : ℝ} (hε : 0 < ε) (w : ℂ) : ρ ε w ≤ 1 / (ε ^ 2 * c0) := by
  unfold ρ
  gcongr
  · exact mul_pos (pow_pos hε 2) c0_pos |>.le
  · exact ρ0_le_one _

lemma integral_ρ {ε : ℝ} (hε : 0 < ε) : ∫ w, ρ ε w = 1 := by
  unfold ρ
  rw [integral_div, Measure.integral_comp_inv_smul_of_nonneg _ _ hε.le, Complex.finrank_real_complex]
  change ε ^ 2 * c0 / (ε ^ 2 * c0) = 1
  exact div_self (mul_pos (pow_pos hε 2) c0_pos).ne'

lemma ρ_radial (ε : ℝ) {w w' : ℂ} (h : ‖w‖ = ‖w'‖) : ρ ε w = ρ ε w' := by
  simp only [ρ, ρ0, norm_smul, h]

lemma ρ_neg (ε : ℝ) (w : ℂ) : ρ ε (-w) = ρ ε w := ρ_radial ε (norm_neg w)

lemma ρ_continuous (ε : ℝ) : Continuous (ρ ε) := (ρ_contDiff ε).continuous

lemma polar_eq_circleMap (z : ℂ) (r θ : ℝ) :
    z + Complex.polarCoord.symm (r, θ) = circleMap z r θ := by
  simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  push_cast; ring

lemma continuous_cpolar : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  rw [this]; fun_prop

/-- polar coordinates for a continuous function supported in `closedBall 0 ε` -/
lemma integral_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℂ → E} (hF : Continuous F) {ε : ℝ} (hε : 0 < ε) (hFs : ∀ w, ε < ‖w‖ → F w = 0) :
    ∫ w, F w = ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (-π) π, r • F (Complex.polarCoord.symm (r, θ)) := by
  rw [← Complex.integral_comp_polarCoord_symm]
  change ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-π) π, _ = _
  rw [Measure.volume_eq_prod]
  apply setIntegral_prod
  have hc : Continuous fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p) :=
    continuous_fst.smul (hF.comp continuous_cpolar)
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := Icc 0 ε ×ˢ Icc (-π) π)
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
  simp only [mem_Ioi, mem_Ioo] at hr hθ
  have : ε < r := by
    by_contra h; push Not at h
    exact hn ⟨⟨hr.le, h⟩, ⟨hθ.1.le, hθ.2.le⟩⟩
  simp only
  rw [hFs, smul_zero]
  rw [Complex.norm_polarCoord_symm, abs_of_pos hr]; exact this

lemma integral_Ioo_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {h : ℂ → E} {z : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R) (hh : DifferentiableOn ℂ h (ball z R)) :
    ∫ θ in Ioo (-π) π, h (z + Complex.polarCoord.symm (r, θ)) = (2 * π) • h z := by
  simp_rw [polar_eq_circleMap]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hp : Function.Periodic (fun θ => h (circleMap z r θ)) (2 * π) :=
    (periodic_circleMap z r).comp h
  have := hp.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  rw [this]
  have hd : DiffContOnCl ℂ h (ball z |r|) := by
    rw [abs_of_pos hr]
    exact hh.diffContOnCl_ball (closedBall_subset_ball hrR)
  have h2 := hd.circleAverage
  rw [Real.circleAverage_def] at h2
  rw [← h2, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

lemma mean_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {h : ℂ → E} {z : ℂ} {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hh : DifferentiableOn ℂ h (ball z R)) :
    ∫ w, ρ ε w • h (z + w) = h z := by
  have hF : Continuous fun w => ρ ε w • h (z + w) := by
    refine ContinuousOn.continuous_of_tsupport_subset (s := ball 0 R) ?_ isOpen_ball ?_
    · refine (ρ_continuous ε).continuousOn.smul ?_
      refine hh.continuousOn.comp (continuous_const.add continuous_id).continuousOn ?_
      intro w hw; simpa [mem_ball, dist_eq_norm] using hw
    · refine (tsupport_smul_subset_left _ _).trans ?_
      refine (closure_mono (ρ_support hε)).trans ?_
      rw [closure_ball _ hε.ne']
      exact closedBall_subset_ball hεR
  have hFs : ∀ w : ℂ, ε < ‖w‖ → ρ ε w • h (z + w) = 0 := fun w hw => by
    rw [ρ_eq_zero hε hw.le, zero_smul]
  have hG : Continuous fun w => ρ ε w • h z := (ρ_continuous ε).smul continuous_const
  have hGs : ∀ w : ℂ, ε < ‖w‖ → ρ ε w • h z = 0 := fun w hw => by
    rw [ρ_eq_zero hε hw.le, zero_smul]
  have key : ∫ w, ρ ε w • h (z + w) = ∫ w, ρ ε w • h z := by
    rw [integral_polar hF hε hFs, integral_polar hG hε hGs]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    simp only [mem_Ioi] at hr
    have hρ : ∀ θ, ρ ε (Complex.polarCoord.symm (r, θ)) = ρ ε r := fun θ =>
      ρ_radial ε (by rw [Complex.norm_polarCoord_symm, Complex.norm_real, Real.norm_eq_abs])
    simp_rw [hρ, smul_smul]
    rw [integral_smul, integral_smul]
    by_cases hrε : r < ε
    · rw [integral_Ioo_circle hr (hrε.trans hεR) hh, setIntegral_const]
      simp only [Real.volume_real_Ioo, sub_neg_eq_add]
      rw [max_eq_left (by linarith [Real.pi_pos]), two_mul]
    · rw [ρ_eq_zero hε (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith)]
      simp
  rw [key, integral_smul_const, integral_ρ hε, one_smul]

section conv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- mollification -/
def conv (U : ℂ → E) (ε : ℝ) (z : ℂ) : E := ∫ t, ρ ε (z - t) • U t

lemma int_smul {U : ℂ → E} (hU : Integrable U) {g : ℂ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) : Integrable (fun t => g t • U t) := by
  refine Integrable.mono' (hU.norm.const_mul C)
    (hg.aestronglyMeasurable.smul hU.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

lemma fderiv_ρ_cont (ε : ℝ) : Continuous (fderiv ℝ (ρ ε)) :=
  (ρ_contDiff ε).continuous_fderiv (by simp)

lemma hasFDerivAt_conv {U : ℂ → E} (hU : Integrable U) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ∃ D : ℂ →L[ℝ] E, HasFDerivAt (conv U ε) D z ∧
      ∀ v, D v = ∫ t, fderiv ℝ (ρ ε) (z - t) v • U t := by
  let L : E →L[ℝ] ℝ →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hc : conv U ε = convolution U (ρ ε) L volume := by
    funext x; simp [conv, convolution_def, L]
  have hloc : LocallyIntegrable U volume := hU.locallyIntegrable
  have h := (ρ_hasCompactSupport hε).hasFDerivAt_convolution_right L hloc
    ((ρ_contDiff ε).of_le (by simp)) z
  rw [← hc] at h
  refine ⟨_, h, fun v => ?_⟩
  have hex := ((ρ_hasCompactSupport hε).fderiv (𝕜 := ℝ)).convolutionExists_right
    (L.precompR ℂ) hloc (fderiv_ρ_cont ε) z
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  simp [L]

/-- Cauchy–Riemann equations for the mollification -/
lemma conv_CR [CompleteSpace E] {U : ℂ → E} (hU : Integrable U)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      ∫ z, (fderiv ℝ φ z 1 • U z + fderiv ℝ φ z Complex.I • (Complex.I • U z)) = 0)
    {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ‖z‖ + ε < 1) :
    DifferentiableAt ℂ (conv U ε) z := by
  obtain ⟨D, hD, hDv⟩ := hasFDerivAt_conv hU hε z
  let φ : ℂ → ℝ := fun w => ρ ε (z - w)
  have hφ : ContDiff ℝ ∞ φ := (ρ_contDiff ε).comp (contDiff_const.sub contDiff_id)
  have hφs : tsupport φ ⊆ closedBall z ε := by
    refine closure_minimal ?_ isClosed_closedBall
    intro w hw
    have := ρ_support hε hw
    simp only [mem_ball, dist_zero_right] at this
    rw [mem_closedBall, dist_comm, dist_eq_norm]; exact this.le
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z ε)
      (subset_closure.trans hφs)
  have hφb : tsupport φ ⊆ ball 0 1 := by
    refine hφs.trans fun w hw => ?_
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hfd : ∀ w v, fderiv ℝ φ w v = - fderiv ℝ (ρ ε) (z - w) v := by
    intro w v
    have : fderiv ℝ φ w = -fderiv ℝ (ρ ε) (z - w) := by
      have h1 : HasFDerivAt φ ((fderiv ℝ (ρ ε) (z - w)).comp (-ContinuousLinearMap.id ℝ ℂ)) w := by
        have h2 := ((ρ_contDiff ε).differentiable (by simp) (z - w)).hasFDerivAt
        exact h2.comp w ((hasFDerivAt_id w).const_sub z)
      rw [h1.fderiv]; ext v; simp
    rw [this]; rfl
  obtain ⟨C, hC⟩ := (fderiv_ρ_cont ε).bounded_above_of_compact_support
    ((ρ_hasCompactSupport hε).fderiv (𝕜 := ℝ))
  have hint : ∀ v : ℂ, Integrable fun t => fderiv ℝ (ρ ε) (z - t) v • U t := by
    intro v
    refine int_smul hU (((fderiv_ρ_cont ε).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const) (C := C * ‖v‖) fun t => ?_
    exact ((fderiv ℝ (ρ ε) (z - t)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have hw := hweak φ hφ hφc hφb
  simp_rw [hfd, neg_smul, smul_comm _ Complex.I] at hw
  rw [integral_add (f := fun t => -(fderiv ℝ (ρ ε) (z - t) 1 • U t))
    (g := fun t => -(Complex.I • (fderiv ℝ (ρ ε) (z - t) Complex.I • U t)))
    (hint 1).neg ((hint Complex.I).smul Complex.I).neg, integral_neg, integral_neg,
    integral_smul, ← hDv, ← hDv] at hw
  have hB : D Complex.I = Complex.I • D 1 := by
    have : Complex.I • (D 1 + Complex.I • D Complex.I) = 0 := by
      rw [show D 1 + Complex.I • D Complex.I = -(-D 1 + -(Complex.I • D Complex.I)) by abel, hw,
        neg_zero, smul_zero]
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul] at this
    exact (eq_of_sub_eq_zero (by rw [← this]; abel)).symm
  let D' : ℂ →L[ℂ] E := (1 : ℂ →L[ℂ] ℂ).smulRight (D 1)
  refine (hasFDerivAt_of_restrictScalars ℝ hD (f' := D') ?_).differentiableAt
  ext v
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  simp only [D', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply]
  calc v • D 1 = ((v.re:ℂ) + v.im * Complex.I) • D 1 := by rw [Complex.re_add_im]
   _ = v.re • D 1 + v.im • (Complex.I • D 1) := by
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
   _ = D v := by rw [← hB, ← map_smul, ← map_smul, ← map_add, ← hv]
lemma ρ_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (ρ ε) :=
  (ρ_continuous ε).integrable_of_hasCompactSupport (ρ_hasCompactSupport hε)

/-- kernel of the iterated mollification -/
def K (δ ε : ℝ) (y : ℂ) : ℝ := ∫ w, ρ δ w * ρ ε (y + w)

lemma K_symm (δ ε : ℝ) (y : ℂ) : K δ ε y = K ε δ y := by
  unfold K
  rw [← integral_sub_left_eq_self _ _ (-y)]
  congr 1; funext w
  rw [show -y - w = -(y + w) by ring, show y + -(y + w) = -w by ring, ρ_neg, ρ_neg, mul_comm]

lemma conv_conv [CompleteSpace E] {U : ℂ → E} (hU : Integrable U) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z : ℂ) :
    ∫ w, ρ δ w • conv U ε (z + w) = ∫ t, K δ ε (z - t) • U t := by
  unfold conv
  simp_rw [← integral_smul, smul_smul]
  have hint : Integrable (Function.uncurry fun w t => (ρ δ w * ρ ε (z + w - t)) • U t)
      (volume.prod volume) := by
    have hb : Integrable (fun p : ℂ × ℂ => ρ δ p.1 * (1 / (ε ^ 2 * c0)) * ‖U p.2‖)
        (volume.prod volume) :=
      ((ρ_integrable hδ).mul_const _).mul_prod hU.norm
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous fun p : ℂ × ℂ => ρ δ p.1 * ρ ε (z + p.1 - p.2) :=
        ((ρ_continuous δ).comp continuous_fst).mul ((ρ_continuous ε).comp
          ((continuous_const.add continuous_fst).sub continuous_snd))
      exact AEStronglyMeasurable.smul (f := fun p : ℂ × ℂ => ρ δ p.1 * ρ ε (z + p.1 - p.2))
        hc.aestronglyMeasurable hU.aestronglyMeasurable.comp_snd
    · show ‖(ρ δ p.1 * ρ ε (z + p.1 - p.2)) • U p.2‖ ≤ _
      simp only [norm_smul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (ρ_nonneg _)]
      gcongr
      · exact ρ_nonneg _
      · exact ρ_le hε _
  rw [integral_integral_swap hint]
  congr 1; funext t
  rw [integral_smul_const]
  congr 1
  unfold K
  congr 1; funext w
  congr 2; ring

lemma conv_eq_conv [CompleteSpace E] {U : ℂ → E} (hU : Integrable U)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      ∫ z, (fderiv ℝ φ z 1 • U z + fderiv ℝ φ z Complex.I • (Complex.I • U z)) = 0)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {z : ℂ} (hz : ‖z‖ + ε + δ < 1) :
    conv U ε z = conv U δ z := by
  have hmv : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ‖z‖ + ε + δ < 1 →
      conv U ε z = ∫ t, K δ ε (z - t) • U t := by
    intro ε δ hε hδ hz
    rw [← conv_conv hU hε hδ z]
    refine (mean_value (R := 1 - ε - ‖z‖) hδ (by linarith) ?_).symm
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    refine (conv_CR hU hweak hε ?_).differentiableWithinAt
    calc ‖y‖ + ε = ‖(y - z) + z‖ + ε := by rw [sub_add_cancel]
      _ ≤ ‖y - z‖ + ‖z‖ + ε := by gcongr; exact norm_add_le _ _
      _ < 1 := by linarith
  rw [hmv ε δ hε hδ hz, hmv δ ε hδ hε (by linarith)]
  simp_rw [K_symm δ ε]

lemma conv_tendsto [CompleteSpace E] {U : ℂ → E} (hU : Integrable U) :
    ∀ᵐ z, Tendsto (fun ε => conv U ε z) (𝓝[>] 0) (𝓝 (U z)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hU.locallyIntegrable 1] with z hz
  have h1 := hz (fun _ => z) id tendsto_id
    (by filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mem_closedBall_self (by simp only [mem_Ioi] at hε; simp; linarith))
  refine tendsto_integral_smul_of_tendsto_average_norm_sub (π / c0) h1
    (Eventually.of_forall fun ε => hU.integrableOn) ?_ ?_ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_sub_left_eq_self (fun y => ρ ε y), integral_ρ hε]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    intro y hy
    have := ρ_support hε hy
    simp only [mem_ball, dist_zero_right] at this
    rw [id, mem_closedBall, dist_comm, dist_eq_norm]; exact this.le
  · filter_upwards [self_mem_nhdsWithin] with ε hε y
    simp only [mem_Ioi] at hε
    rw [abs_of_nonneg (ρ_nonneg _), id, measureReal_def, Complex.volume_closedBall]
    refine (ρ_le hε _).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]
    simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
    have := c0_pos
    field_simp

end conv

end

end WeylDev

open MeasureTheory Metric Filter Topology Set DbarRegularity WeylDev
open scoped ContDiff ENNReal NNReal Real

theorem solution (n : ℕ)
    (u : ℂ → EuclideanSpace ℂ (Fin n)) (hu : IntegrableOn u (ball 0 1))
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      ∫ z, (fderiv ℝ φ z 1 • u z + fderiv ℝ φ z Complex.I • (Complex.I • u z)) = 0) :
    ∃ v : ℂ → EuclideanSpace ℂ (Fin n), DifferentiableOn ℂ v (ball 0 1) ∧
      u =ᵐ[volume.restrict (ball 0 1)] v := by
  set U := (ball (0:ℂ) 1).indicator u with hUdef
  have hU : Integrable U := (integrable_indicator_iff measurableSet_ball).2 hu
  have hweakU : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      ∫ z, (fderiv ℝ φ z 1 • U z + fderiv ℝ φ z Complex.I • (Complex.I • U z)) = 0 := by
    intro φ h1 h2 h3
    rw [← hweak φ h1 h2 h3]
    congr 1; funext w
    by_cases hw : w ∈ ball (0:ℂ) 1
    · rw [hUdef, indicator_of_mem hw]
    · have : w ∉ tsupport φ := fun h => hw (h3 h)
      rw [fderiv_of_notMem_tsupport ℝ this]
      simp
  refine ⟨fun z => conv U ((1 - ‖z‖) / 3) z, ?_, ?_⟩
  · intro z0 hz0
    rw [mem_ball, dist_zero_right] at hz0
    have hε0 : 0 < (1 - ‖z0‖) / 3 := by linarith
    have hev : (fun z => conv U ((1 - ‖z‖) / 3) z) =ᶠ[𝓝 z0] conv U ((1 - ‖z0‖) / 3) := by
      have : ∀ᶠ z in 𝓝 z0, ‖z‖ < (1 + ‖z0‖) / 2 :=
        (continuous_norm.tendsto z0).eventually (gt_mem_nhds (by linarith))
      filter_upwards [this] with z hz
      exact conv_eq_conv hU hweakU (by linarith) hε0 (by linarith)
    exact ((conv_CR hU hweakU hε0 (by linarith)).congr_of_eventuallyEq hev).differentiableWithinAt
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [conv_tendsto hU] with z hz hzb
    rw [mem_ball, dist_zero_right] at hzb
    have hU' : U z = u z := by rw [hUdef, indicator_of_mem (by simpa using hzb)]
    rw [← hU']
    refine tendsto_nhds_unique hz (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < (1 - ‖z‖) / 3 by linarith)] with ε hε
    exact conv_eq_conv hU hweakU (by linarith [hε.1, hε.2]) hε.1 (by linarith [hε.1, hε.2])
