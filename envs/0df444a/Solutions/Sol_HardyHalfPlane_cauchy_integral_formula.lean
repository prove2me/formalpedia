-- Prove2me | solution 1 for HardyHalfPlane.cauchy_integral_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:22:55.481422+00:00
-- url     : https://prove2.me/submissions/b7fb133f-5310-47d9-92fb-2290ba35864d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy
import Theorems.Thm_MasulloGRH_asymptotic_cauchy_value_formula_with_channel_bound
import Theorems.Thm_HardyHalfPlane_tendsto_eLpNorm_sub_boundary_function

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace Sol_HardyHalfPlane_cauchy_integral_formula

open Complex HardyHalfPlane

/-! ### The Cauchy kernel on a vertical line -/

lemma re_ker (c y : ℝ) (z : ℂ) : ((c:ℂ) + (y:ℂ) * I - z).re = c - z.re := by simp

lemma im_ker (c y : ℝ) (z : ℂ) : ((c:ℂ) + (y:ℂ) * I - z).im = y - z.im := by simp

lemma abs_le_norm_ker (c y : ℝ) (z : ℂ) : |c - z.re| ≤ ‖(c:ℂ) + (y:ℂ) * I - z‖ := by
  have := Complex.abs_re_le_norm ((c:ℂ) + (y:ℂ) * I - z)
  rwa [re_ker] at this

lemma ker_ne (c y : ℝ) (z : ℂ) (hz : z.re ≠ c) : (c:ℂ) + (y:ℂ) * I - z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_ker, Complex.zero_re] at this
  exact hz (by linarith)

lemma continuous_ker (c : ℝ) (z : ℂ) (hz : z.re ≠ c) :
    Continuous (fun y : ℝ => 1 / ((c:ℂ) + (y:ℂ) * I - z)) :=
  Continuous.div continuous_const (by fun_prop) (fun y => ker_ne c y z hz)

lemma norm_ker_lower (c y : ℝ) (z : ℂ) (hz : z.re ≠ c) :
    min |c - z.re| 1 / (2 * (1 + |z.im|)) * (1 + |y|) ≤ ‖(c:ℂ) + (y:ℂ) * I - z‖ := by
  set w := (c:ℂ) + (y:ℂ) * I - z
  have h1 : |c - z.re| ≤ ‖w‖ := abs_le_norm_ker c y z
  have h2 : |y - z.im| ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w; rwa [im_ker] at this
  set m := min |c - z.re| 1
  have hm0 : 0 < m := lt_min (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))) one_pos
  have hm1 : m ≤ |c - z.re| := min_le_left _ _
  have hm2 : m ≤ 1 := min_le_right _ _
  have h3 : 1 + |y| ≤ (1 + |z.im|) * (1 + |y - z.im|) := by
    have := abs_sub_abs_le_abs_sub y z.im
    nlinarith [abs_nonneg z.im, abs_nonneg (y - z.im)]
  have h4 : m * (1 + |y - z.im|) ≤ 2 * ‖w‖ := by
    nlinarith [abs_nonneg (y - z.im), mul_le_mul_of_nonneg_right hm2 (abs_nonneg (y - z.im))]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h3 hm0.le,
    mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 1 + |z.im|)]

lemma ker_memLp (c : ℝ) (z : ℂ) (hz : z.re ≠ c) {q : ℝ≥0∞} (hq : 1 < q) :
    MemLp (fun y : ℝ => 1 / ((c:ℂ) + (y:ℂ) * I - z)) q volume := by
  have hcont := continuous_ker c z hz
  have hδ : 0 < |c - z.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))
  by_cases hqt : q = ⊤
  · subst hqt
    refine memLp_top_of_bound hcont.aestronglyMeasurable (1 / |c - z.re|)
      (Eventually.of_forall fun y => ?_)
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ (abs_le_norm_ker c y z)
  · have hq0 : q ≠ 0 := (lt_trans zero_lt_one hq).ne'
    rw [← integrable_norm_rpow_iff hcont.aestronglyMeasurable hq0 hqt]
    set r := q.toReal
    have hr : 1 < r := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt).mpr hq
      simpa using this
    set κ := min |c - z.re| 1 / (2 * (1 + |z.im|))
    have hκ : 0 < κ := by
      have : 0 < min |c - z.re| 1 := lt_min hδ one_pos
      positivity
    have hint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-r)) volume :=
      integrable_one_add_norm (by simpa using hr)
    refine (hint.const_mul (κ⁻¹ ^ r)).mono'
      ((hcont.norm.rpow_const fun _ => Or.inr (by linarith)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    have hw : κ * (1 + |y|) ≤ ‖(c:ℂ) + (y:ℂ) * I - z‖ := norm_ker_lower c y z hz
    have hk : ‖1 / ((c:ℂ) + (y:ℂ) * I - z)‖ ≤ κ⁻¹ * (1 + ‖y‖)⁻¹ := by
      rw [norm_div, norm_one, Real.norm_eq_abs, ← mul_inv, one_div]
      exact inv_anti₀ (by positivity) hw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖1 / ((c:ℂ) + (y:ℂ) * I - z)‖ ^ r ≤ (κ⁻¹ * (1 + ‖y‖)⁻¹) ^ r :=
          Real.rpow_le_rpow (norm_nonneg _) hk (by linarith)
      _ = κ⁻¹ ^ r * (1 + ‖y‖) ^ (-r) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
            Real.inv_rpow hκ.le, Real.inv_rpow (by positivity : (0:ℝ) ≤ 1 + ‖y‖)]

lemma norm_ker_le_two (c σ y : ℝ) (z : ℂ) (h : |σ - c| ≤ |c - z.re| / 2) :
    ‖(c:ℂ) + (y:ℂ) * I - z‖ ≤ 2 * ‖(σ:ℂ) + (y:ℂ) * I - z‖ := by
  have e : (c:ℂ) + (y:ℂ) * I - z = ((σ:ℂ) + (y:ℂ) * I - z) + ((c - σ : ℝ) : ℂ) := by
    push_cast; ring
  have h1 : ‖(c:ℂ) + (y:ℂ) * I - z‖ ≤ ‖(σ:ℂ) + (y:ℂ) * I - z‖ + |c - σ| := by
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : |σ - z.re| ≤ ‖(σ:ℂ) + (y:ℂ) * I - z‖ := abs_le_norm_ker σ y z
  have h3 : |c - z.re| ≤ |c - σ| + |σ - z.re| := abs_sub_le c σ z.re
  rw [abs_sub_comm] at h
  linarith

/-! ### Functions on vertical lines -/

lemma line_continuous (Φ : ℂ → ℂ) (a : ℝ) (hd : DifferentiableOn ℂ Φ {s : ℂ | s.re < a})
    (σ : ℝ) (hσ : σ < a) : Continuous (fun y : ℝ => Φ ((σ:ℂ) + (y:ℂ) * I)) := by
  refine hd.continuousOn.comp_continuous (by fun_prop) (fun y => ?_)
  simpa using hσ

lemma line_memLp (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hΦ : MemLeftHardy Φ a p) (σ : ℝ)
    (hσ : σ < a) : MemLp (fun y : ℝ => Φ ((σ:ℂ) + (y:ℂ) * I)) p volume := by
  refine ⟨(line_continuous Φ a hΦ.1 σ hσ).aestronglyMeasurable, lt_of_le_of_lt ?_ hΦ.2⟩
  unfold leftHardyNorm
  exact le_iSup₂ (f := fun σ (_ : σ < a) =>
    eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume) σ hσ

lemma one_lt_conjExponent {p : ℝ≥0∞} (_hp1 : 1 ≤ p) (hp : p ≠ ⊤) : 1 < p.conjExponent := by
  rw [ENNReal.conjExponent]
  have : (p - 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.sub_ne_top hp)
  exact ENNReal.lt_add_right ENNReal.one_ne_top this

/-! ### A bounded holomorphic regularizer with rapid vertical decay -/

/-- `W a s = (a - s)^{1/2}` (principal branch, written with `exp ∘ log`). -/
noncomputable def W (a : ℝ) (s : ℂ) : ℂ := Complex.exp (Complex.log ((a:ℂ) - s) / 2)

/-- `G a n s = exp (-(n+1)⁻¹ (a - s)^{1/2})`. -/
noncomputable def G (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-((((n:ℝ) + 1)⁻¹ : ℝ) : ℂ) * W a s)

lemma W_re (a : ℝ) (s : ℂ) : (W a s).re =
    Real.exp (Real.log ‖(a:ℂ) - s‖ / 2) * Real.cos (Complex.arg ((a:ℂ) - s) / 2) := by
  simp [W, Complex.exp_re, Complex.log_re, Complex.log_im]

lemma cos_half_arg (w : ℂ) (hw : 0 ≤ w.re) : 1 / 2 ≤ Real.cos (Complex.arg w / 2) := by
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr hw
  have h1 : |Complex.arg w / 2| ≤ Real.pi / 4 := by
    rw [abs_div, abs_two]; linarith
  rw [← Real.cos_abs]
  have hs : (1:ℝ) ≤ √2 := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  calc (1:ℝ) / 2 ≤ √2 / 2 := by linarith
    _ = Real.cos (Real.pi / 4) := Real.cos_pi_div_four.symm
    _ ≤ Real.cos |Complex.arg w / 2| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h1

lemma W_re_nonneg (a : ℝ) (s : ℂ) (hs : s.re ≤ a) : 0 ≤ (W a s).re := by
  rw [W_re]
  have := cos_half_arg ((a:ℂ) - s) (by simp; linarith)
  exact mul_nonneg (Real.exp_pos _).le (by linarith)

lemma norm_G (a : ℝ) (n : ℕ) (s : ℂ) :
    ‖G a n s‖ = Real.exp (-(((n:ℝ) + 1)⁻¹ * (W a s).re)) := by
  rw [G, Complex.norm_exp]
  congr 1
  rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]

lemma norm_G_le_one (a : ℝ) (n : ℕ) (s : ℂ) (hs : s.re ≤ a) : ‖G a n s‖ ≤ 1 := by
  rw [norm_G, Real.exp_le_one_iff]
  have h1 := W_re_nonneg a s hs
  have h2 : 0 < ((n:ℝ) + 1)⁻¹ := by positivity
  nlinarith

lemma G_decay (a : ℝ) (n N : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, s.re ≤ a → 1 ≤ |s.im| → ‖G a n s‖ ≤ C / |s.im| ^ N := by
  set t := ((n:ℝ) + 1)⁻¹ with ht_def
  have ht : 0 < t := by positivity
  refine ⟨((2 * N).factorial : ℝ) / (t / 2) ^ (2 * N), by positivity, fun s hs hy => ?_⟩
  set w := (a:ℂ) - s with hw_def
  have hwre : 0 ≤ w.re := by simp [w]; linarith
  have hy0 : 0 < |s.im| := by linarith
  have hwn : |s.im| ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    simpa [w] using this
  set v := Real.exp (Real.log |s.im| / 2) with hv_def
  have hv0 : 0 < v := Real.exp_pos _
  have hv2 : v ^ 2 = |s.im| := by
    rw [hv_def, ← Real.exp_nat_mul]
    push_cast
    rw [show (2:ℝ) * (Real.log |s.im| / 2) = Real.log |s.im| by ring, Real.exp_log hy0]
  have hvle : v ≤ Real.exp (Real.log ‖w‖ / 2) := by
    rw [hv_def]
    exact Real.exp_le_exp.mpr (by
      have := Real.log_le_log hy0 hwn
      linarith)
  have hre : 1 / 2 * v ≤ (W a s).re := by
    rw [W_re]
    have hc := cos_half_arg w hwre
    have he := Real.exp_pos (Real.log ‖w‖ / 2)
    nlinarith
  set u := t / 2 * v with hu_def
  have hu : 0 < u := by positivity
  have hG : ‖G a n s‖ ≤ Real.exp (-u) := by
    rw [norm_G]
    exact Real.exp_le_exp.mpr (by rw [hu_def]; nlinarith)
  have hfac := Real.pow_div_factorial_le_exp u hu.le (2 * N)
  have hexp : Real.exp (-u) ≤ ((2 * N).factorial : ℝ) / u ^ (2 * N) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos u) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hfac
    linarith
  have hu2 : u ^ (2 * N) = (t / 2) ^ (2 * N) * |s.im| ^ N := by
    rw [hu_def, mul_pow, pow_mul v, hv2]
  calc ‖G a n s‖ ≤ Real.exp (-u) := hG
    _ ≤ ((2 * N).factorial : ℝ) / u ^ (2 * N) := hexp
    _ = ((2 * N).factorial : ℝ) / (t / 2) ^ (2 * N) / |s.im| ^ N := by rw [hu2, div_div]

lemma G_tendsto (a : ℝ) (s : ℂ) : Tendsto (fun n : ℕ => G a n s) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => ((((n:ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [one_div] at this
    have h := (Complex.continuous_ofReal.tendsto 0).comp this
    rw [Complex.ofReal_zero] at h
    exact h
  have := ((h0.neg).mul_const (W a s)).cexp
  simpa [G] using this

lemma G_differentiableAt (a : ℝ) (n : ℕ) (s : ℂ) (hs : s.re < a) :
    DifferentiableAt ℂ (G a n) s := by
  have hslit : (a:ℂ) - s ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp; linarith
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Complex.log ((a:ℂ) - s)) s :=
    (differentiableAt_const _ |>.sub differentiableAt_id).clog hslit
  have h2 : DifferentiableAt ℂ (W a) s := (h1.div_const 2).cexp
  exact ((h2.const_mul _).cexp)

/-! ### Pointwise bound for Hardy functions: `|Φ(s)|^p ≤ 2 ‖Φ‖^p / (π (a - Re s))` -/

lemma circ_eq (s : ℂ) (ρ θ : ℝ) :
    circleMap s ρ θ = s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) := by
  simp [circleMap, Complex.exp_mul_I]

/-- Sub-mean value property of `‖f‖` on circles. -/
lemma norm_le_circle (f : ℂ → ℂ) (s : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.closedBall s ρ)) :
    2 * Real.pi * ‖f s‖ ≤
      ∫ θ in (-Real.pi)..Real.pi, ‖f (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖ := by
  have hd : DiffContOnCl ℂ f (Metric.ball s |ρ|) := by
    apply DifferentiableOn.diffContOnCl
    rwa [abs_of_pos hρ, closure_ball s hρ.ne']
  have h1 := hd.circleAverage
  rw [Real.circleAverage_def] at h1
  set F : ℝ → ℝ := fun θ => ‖f (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖ with hF
  have hper : Function.Periodic F (2 * Real.pi) := by
    intro θ; simp only [hF]; push_cast; rw [Complex.cos_add_two_pi, Complex.sin_add_two_pi]
  have hshift := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [show (0:ℝ) + 2 * Real.pi = 2 * Real.pi by ring,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] at hshift
  have hpi : 0 < 2 * Real.pi := by positivity
  have h2 : ‖f s‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap s ρ θ)‖ := by
    rw [← h1, norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm hpi.le
  have h3 : ∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap s ρ θ)‖ = ∫ θ in (0:ℝ)..2 * Real.pi, F θ := by
    congr 1; funext θ; rw [circ_eq]
  rw [h3, hshift] at h2
  have := mul_le_mul_of_nonneg_left h2 hpi.le
  rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at this

lemma polar_norm (p : ℝ × ℝ) (hp : 0 < p.1) :
    ‖(p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I)‖ = p.1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
  have : ‖(Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I‖ = 1 := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    exact Complex.norm_exp_ofReal_mul_I p.2
  rw [this, mul_one]

/-- Area lower bound from circle lower bounds, via polar coordinates. -/
lemma area_lower (Ψ : ℂ → ℂ) (hΨ : Continuous Ψ) (s : ℂ) (R : ℝ) (hR : 0 < R) (A : ℝ)
    (hA : 0 ≤ A) (hcirc : ∀ ρ ∈ Set.Ioo 0 R,
      2 * Real.pi * A ≤
        ∫ θ in (-Real.pi)..Real.pi, ‖Ψ (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖) :
    ENNReal.ofReal (Real.pi * R ^ 2 * A) ≤ ∫⁻ w in Metric.ball s R, ‖Ψ w‖ₑ := by
  set F : ℂ → ℝ≥0∞ := (Metric.ball (0:ℂ) R).indicator (fun w => ‖Ψ (s + w)‖ₑ) with hF
  have hFm : Measurable F :=
    (Measurable.indicator (hΨ.comp (continuous_const.add continuous_id)).measurable.enorm
      Metric.isOpen_ball.measurableSet)
  have step1 : ∫⁻ w in Metric.ball s R, ‖Ψ w‖ₑ = ∫⁻ w, F w := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_add_left_eq_self _ s]
    congr 1; funext w
    simp only [hF, Set.indicator, Metric.mem_ball, dist_zero_right, dist_self_add_left]
  set G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 *
    ‖Ψ (s + p.1 * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I))‖ₑ with hG
  have hGm : Measurable G := by
    simp only [hG]
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
    exact (hΨ.comp (by fun_prop)).measurable.enorm
  have step2 : ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p ≤ ∫⁻ w, F w := by
    rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
    calc ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p
        = ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) := by
          refine setLIntegral_congr_fun
            (measurableSet_Ioo.prod measurableSet_Ioo) (fun p hp => ?_)
          have hp1 : 0 < p.1 := hp.1.1
          have hpR : p.1 < R := hp.1.2
          simp only [hG, hF, Complex.polarCoord_symm_apply, smul_eq_mul]
          rw [Set.indicator_of_mem]
          rw [Metric.mem_ball, dist_zero_right, polar_norm p hp1]
          exact hpR
      _ ≤ _ := lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioi_self subset_rfl)
  have step3 : ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p =
      ∫⁻ ρ in Set.Ioo 0 R, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, G (ρ, θ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hGm.aemeasurable]
  have step4 : ∀ ρ ∈ Set.Ioo 0 R, ENNReal.ofReal (2 * Real.pi * A) * ENNReal.ofReal ρ ≤
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, G (ρ, θ) := by
    intro ρ hρ
    have hc : Continuous (fun θ : ℝ =>
        ‖Ψ (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖) :=
      (hΨ.comp (by fun_prop)).norm
    have hm : Measurable (fun θ : ℝ =>
        ‖Ψ (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖ₑ) :=
      (hΨ.comp (by fun_prop)).measurable.enorm
    simp only [hG]
    rw [lintegral_const_mul _ hm, mul_comm]
    gcongr
    have hint : Integrable (fun θ : ℝ =>
        Ψ (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)))
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
      ((hΨ.comp (by fun_prop)).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    apply ENNReal.ofReal_le_ofReal
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact hcirc ρ hρ
  have step5 : ∫⁻ ρ in Set.Ioo 0 R, ENNReal.ofReal ρ = ENNReal.ofReal (R ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le, integral_id]
      ring
    · exact (continuous_id.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun ρ hρ => hρ.1.le)
  calc ENNReal.ofReal (Real.pi * R ^ 2 * A)
      = ENNReal.ofReal (2 * Real.pi * A) * ENNReal.ofReal (R ^ 2 / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    _ = ∫⁻ ρ in Set.Ioo 0 R, ENNReal.ofReal (2 * Real.pi * A) * ENNReal.ofReal ρ := by
        rw [lintegral_const_mul _ ENNReal.measurable_ofReal, step5]
    _ ≤ ∫⁻ ρ in Set.Ioo 0 R, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, G (ρ, θ) :=
        setLIntegral_mono' measurableSet_Ioo step4
    _ = ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p := step3.symm
    _ ≤ ∫⁻ w, F w := step2
    _ = ∫⁻ w in Metric.ball s R, ‖Ψ w‖ₑ := step1.symm

/-- Integral of `|Ψ|^r` over a vertical strip, by Tonelli in Cartesian coordinates. -/
lemma strip_upper (Ψ : ℂ → ℂ) (hΨ : Continuous Ψ) (x0 R r : ℝ) (B : ℝ≥0∞)
    (hline : ∀ x ∈ Set.Ioo (x0 - R) (x0 + R),
      ∫⁻ y : ℝ, ‖Ψ ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ r ≤ B) :
    ∫⁻ w in {w : ℂ | x0 - R < w.re ∧ w.re < x0 + R}, ‖Ψ w‖ₑ ^ r ≤
      ENNReal.ofReal (2 * R) * B := by
  set S := {w : ℂ | x0 - R < w.re ∧ w.re < x0 + R} with hS_def
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const Complex.measurable_re).inter
      (measurableSet_lt Complex.measurable_re measurable_const)
  set f : ℂ → ℝ≥0∞ := S.indicator (fun w => ‖Ψ w‖ₑ ^ r) with hf_def
  have hfm : Measurable f := (hΨ.measurable.enorm.pow_const r).indicator hS
  rw [← lintegral_indicator hS]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  rw [← hmp.lintegral_comp hfm, Measure.volume_eq_prod,
    lintegral_prod (fun q : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm q))
      (hfm.comp hmp.measurable).aemeasurable]
  have hval : ∀ x y : ℝ, Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + (y : ℂ) * I := by
    intro x y
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
  calc ∫⁻ x : ℝ, ∫⁻ y : ℝ, f (Complex.measurableEquivRealProd.symm (x, y))
      ≤ ∫⁻ x : ℝ, (Set.Ioo (x0 - R) (x0 + R)).indicator (fun _ => B) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Set.Ioo (x0 - R) (x0 + R)
        · rw [Set.indicator_of_mem hx]
          calc ∫⁻ y : ℝ, f (Complex.measurableEquivRealProd.symm (x, y))
              = ∫⁻ y : ℝ, ‖Ψ ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ r := by
                congr 1; funext y
                rw [hval, hf_def, Set.indicator_of_mem]
                simpa [hS_def] using hx
            _ ≤ B := hline x hx
        · rw [Set.indicator_of_notMem hx]
          have : ∀ y : ℝ, f (Complex.measurableEquivRealProd.symm (x, y)) = 0 := by
            intro y
            rw [hval, hf_def, Set.indicator_of_notMem]
            simpa [hS_def] using hx
          rw [lintegral_congr this, lintegral_zero]
    _ = B * volume (Set.Ioo (x0 - R) (x0 + R)) := lintegral_indicator_const measurableSet_Ioo B
    _ = ENNReal.ofReal (2 * R) * B := by
        rw [Real.volume_Ioo, mul_comm]; congr 2; ring

theorem norm_rpow_le (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) (s : ℂ) (hs : s.re < a) :
    ‖Φ s‖ ^ p.toReal ≤
      2 / (Real.pi * (a - s.re)) * (leftHardyNorm Φ a p).toReal ^ p.toReal := by
  set d := a - s.re with hd_def
  have hd : 0 < d := by linarith
  set r := p.toReal with hr_def
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hr1 : 1 ≤ r := by
    have := ENNReal.toReal_mono hp hp1
    simpa using this
  have hr0 : 0 < r := by linarith
  set M := leftHardyNorm Φ a p with hM_def
  have hMt : M ≠ ⊤ := hΦ.2.ne
  set m := M.toReal with hm_def
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have key : ∀ R : ℝ, 0 < R → R < d → ‖Φ s‖ ^ r ≤ 2 / (Real.pi * R) * m ^ r := by
    intro R hR hRd
    set b := a - (d - R) / 2 with hb
    have hbR : s.re + R < b := by rw [hb, hd_def]; linarith
    have hba : b < a := by linarith
    set Ψ : ℂ → ℂ := fun w => Φ (((min w.re b : ℝ) : ℂ) + (w.im : ℂ) * I) with hΨ_def
    have hΨc : Continuous Ψ := by
      refine hΦ.1.continuousOn.comp_continuous (by fun_prop) (fun w => ?_)
      show (((min w.re b : ℝ) : ℂ) + (w.im : ℂ) * I).re < a
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact lt_of_le_of_lt (min_le_right _ _) hba
    have hΨeq : ∀ w : ℂ, w.re ≤ b → Ψ w = Φ w := by
      intro w hw
      simp only [hΨ_def, min_eq_left hw]
      rw [Complex.re_add_im]
    have hcirc : ∀ ρ ∈ Set.Ioo 0 R, 2 * Real.pi * ‖Φ s‖ ≤
        ∫ θ in (-Real.pi)..Real.pi, ‖Ψ (s + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖ := by
      intro ρ hρ
      have hsub : Metric.closedBall s ρ ⊆ {w : ℂ | w.re < a} := by
        intro w hw
        have h1 : |w.re - s.re| ≤ ρ := by
          have := Complex.abs_re_le_norm (w - s)
          rw [Complex.sub_re] at this
          rw [Metric.mem_closedBall, dist_eq_norm] at hw
          linarith
        show w.re < a
        have := (abs_le.mp h1).2
        linarith [hρ.2]
      have h := norm_le_circle Φ s ρ hρ.1 (hΦ.1.mono hsub)
      refine h.trans_eq (intervalIntegral.integral_congr (fun θ _ => ?_))
      rw [hΨeq]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one]
      nlinarith [Real.cos_le_one θ, hρ.1, hρ.2]
    have hlow := area_lower Ψ hΨc s R hR ‖Φ s‖ (norm_nonneg _) hcirc
    set S := {w : ℂ | s.re - R < w.re ∧ w.re < s.re + R} with hS_def
    have hball_sub : Metric.ball s R ⊆ S := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have := Complex.abs_re_le_norm (w - s)
      rw [Complex.sub_re] at this
      have h2 := abs_lt.mp (lt_of_le_of_lt this hw)
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hhol : ∫⁻ w in Metric.ball s R, ‖Ψ w‖ₑ ≤
        (∫⁻ w in S, ‖Ψ w‖ₑ ^ r) ^ (1 / r) * (volume (Metric.ball s R)) ^ (1 - 1 / r) := by
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Metric.ball s R))
        (p := 1) (q := p) hp1 hΨc.aestronglyMeasurable
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp,
        Measure.restrict_apply_univ] at this
      simp only [ENNReal.toReal_one, div_one] at this
      refine this.trans ?_
      gcongr
    have hstrip : ∫⁻ w in S, ‖Ψ w‖ₑ ^ r ≤ ENNReal.ofReal (2 * R) * M ^ r := by
      refine strip_upper Ψ hΨc s.re R r (M ^ r) (fun x hx => ?_)
      have hxa : x < a := by linarith [hx.2]
      have hxb : x ≤ b := by linarith [hx.2]
      have h1 : ∫⁻ y : ℝ, ‖Ψ ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ r =
          ∫⁻ y : ℝ, ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ r := by
        congr 1; funext y; rw [hΨeq _ (by simpa using hxb)]
      rw [h1]
      have h2 : eLpNorm (fun y : ℝ => Φ ((x : ℂ) + (y : ℂ) * I)) p volume ≤ M := by
        rw [hM_def]; unfold leftHardyNorm
        exact le_iSup₂ (f := fun σ (_ : σ < a) =>
          eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume) x hxa
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp] at h2
      have := ENNReal.rpow_le_rpow h2 hr0.le
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one] at this
    -- combine
    set V := Real.pi * R ^ 2 with hV_def
    have hV0 : 0 < V := by positivity
    have hV : volume (Metric.ball s R) = ENNReal.ofReal V := by
      rw [Complex.volume_ball, hV_def, ENNReal.ofReal_mul Real.pi_pos.le,
        ENNReal.ofReal_pow hR.le, mul_comm]
      congr 1
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    have hMm : M = ENNReal.ofReal m := (ENNReal.ofReal_toReal hMt).symm
    clear_value V
    have hchain : ENNReal.ofReal (V * ‖Φ s‖) ≤
        ENNReal.ofReal ((2 * R * m ^ r) ^ (1 / r) * V ^ (1 - 1 / r)) := by
      have h1 : 0 ≤ 1 - 1 / r := by
        rw [sub_nonneg, div_le_one hr0]; exact hr1
      calc ENNReal.ofReal (V * ‖Φ s‖) ≤ ∫⁻ w in Metric.ball s R, ‖Ψ w‖ₑ := hlow
        _ ≤ (∫⁻ w in S, ‖Ψ w‖ₑ ^ r) ^ (1 / r) * (volume (Metric.ball s R)) ^ (1 - 1 / r) := hhol
        _ ≤ (ENNReal.ofReal (2 * R) * M ^ r) ^ (1 / r) * (ENNReal.ofReal V) ^ (1 - 1 / r) := by
            rw [hV]; gcongr
        _ = ENNReal.ofReal ((2 * R * m ^ r) ^ (1 / r) * V ^ (1 - 1 / r)) := by
            rw [hMm, ENNReal.ofReal_rpow_of_nonneg hm0 hr0.le, ← ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
              ENNReal.ofReal_rpow_of_nonneg hV0.le h1, ← ENNReal.ofReal_mul (by positivity)]
    have hreal : V * ‖Φ s‖ ≤ (2 * R * m ^ r) ^ (1 / r) * V ^ (1 - 1 / r) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
    have e1 := Real.rpow_le_rpow (by positivity) hreal hr0.le
    have hA0 : 0 ≤ 2 * R * m ^ r := by positivity
    have l1 : (V * ‖Φ s‖) ^ r = V ^ r * ‖Φ s‖ ^ r := Real.mul_rpow hV0.le (norm_nonneg _)
    have l2 : ((2 * R * m ^ r) ^ (1 / r) * V ^ (1 - 1 / r)) ^ r = 2 * R * m ^ r * (V ^ r / V) := by
      rw [Real.mul_rpow (x := (2 * R * m ^ r) ^ (1 / r)) (y := V ^ (1 - 1 / r))
          (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hV0.le _),
        ← Real.rpow_mul hA0, ← Real.rpow_mul hV0.le, one_div_mul_cancel hr0.ne', Real.rpow_one,
        show (1 - 1 / r) * r = r - 1 by field_simp, Real.rpow_sub_one hV0.ne']
    rw [l1, l2] at e1
    have hVr : 0 < V ^ r := Real.rpow_pos_of_pos hV0 r
    have e2 : ‖Φ s‖ ^ r ≤ 2 * R * m ^ r / V := by
      rw [le_div_iff₀ hV0]
      have : V ^ r * ‖Φ s‖ ^ r ≤ V ^ r * (2 * R * m ^ r / V) := by
        calc V ^ r * ‖Φ s‖ ^ r ≤ 2 * R * m ^ r * (V ^ r / V) := e1
          _ = V ^ r * (2 * R * m ^ r / V) := by ring
      have := le_of_mul_le_mul_left this hVr
      rwa [le_div_iff₀ hV0] at this
    calc ‖Φ s‖ ^ r ≤ 2 * R * m ^ r / V := e2
      _ = 2 / (Real.pi * R) * m ^ r := by
          rw [hV_def]; field_simp
  -- let `R → d`
  have hlim : Tendsto (fun R : ℝ => 2 / (Real.pi * R) * m ^ r) (𝓝[<] d)
      (𝓝 (2 / (Real.pi * d) * m ^ r)) := by
    have : ContinuousAt (fun R : ℝ => 2 / (Real.pi * R) * m ^ r) d := by
      refine ((continuousAt_const.div (continuousAt_const.mul continuousAt_id) ?_).mul
        continuousAt_const)
      exact mul_ne_zero Real.pi_pos.ne' hd.ne'
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ R in 𝓝[<] d, ‖Φ s‖ ^ r ≤ 2 / (Real.pi * R) * m ^ r := by
    have h1 : ∀ᶠ R in 𝓝[<] d, 0 < R := (lt_mem_nhds hd).filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, self_mem_nhdsWithin] with R hR hRd using key R hR hRd
  exact ge_of_tendsto hlim hev

/-! ### Boundedness on smaller half-planes -/

lemma bdd (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ≤ a - ε → ‖Φ s‖ ≤ B := by
  set r := p.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos (by positivity) hp
  set M := (leftHardyNorm Φ a p).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨(2 / (Real.pi * ε) * M ^ r) ^ (1 / r), by positivity, fun s hs => ?_⟩
  have h1 := norm_rpow_le Φ a p hp1 hp hΦ s (by linarith)
  have h2 : 2 / (Real.pi * (a - s.re)) * M ^ r ≤ 2 / (Real.pi * ε) * M ^ r := by
    have hpi := Real.pi_pos
    gcongr
    linarith
  calc ‖Φ s‖ = (‖Φ s‖ ^ r) ^ (1 / r) := by
        rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hr.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (h1.trans h2) (by positivity)

/-! ### The formula on interior lines `Re s = a' < a` -/

theorem interior (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) (a' : ℝ) (ha' : a' < a) (z : ℂ) (hz : z.re ≠ a') :
    Integrable (fun y : ℝ => Φ ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z)) volume ∧
      (1 / (2 * (Real.pi : ℂ))) *
          ∫ y : ℝ, Φ ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z) =
        if z.re < a' then Φ z else 0 := by
  have hq : p.HolderConjugate p.conjExponent := .conjExponent hp1
  have hq1 : 1 < p.conjExponent := one_lt_conjExponent hp1 hp
  have hint : Integrable
      (fun y : ℝ => Φ ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z)) volume := by
    have := (line_memLp Φ a p hΦ a' ha').integrable_mul (ker_memLp a' z hz hq1)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  refine ⟨hint, ?_⟩
  set F : ℕ → ℂ → ℂ := fun n s => Φ s * G a n s with hF
  -- hypotheses of the asymptotic Cauchy formula for `F n`
  have hdiff : ∀ n, DifferentiableOn ℂ (F n) {s : ℂ | s.re < a} := fun n =>
    hΦ.1.mul (fun s hs => (G_differentiableAt a n s hs).differentiableWithinAt)
  have hsch : ∀ n, MasulloGRH.SchwartzOnLeftHalfPlane (F n) a := by
    intro n ε hε N _
    obtain ⟨B, hB0, hB⟩ := bdd Φ a p hp1 hp hΦ ε hε
    obtain ⟨C, hC0, hC⟩ := G_decay a n N
    refine ⟨(B + 1) * C, by positivity, 1, fun s hs hy => ?_⟩
    have hy0 : 0 < |s.im| ^ N := pow_pos (by linarith) N
    calc ‖F n s‖ = ‖Φ s‖ * ‖G a n s‖ := norm_mul _ _
      _ ≤ (B + 1) * (C / |s.im| ^ N) := by
          gcongr
          · linarith [hB s hs]
          · exact hC s (by linarith) hy
      _ = (B + 1) * C / |s.im| ^ N := by ring
  have hchan : ∀ n, ∀ Y : ℝ, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ a' → |s.im| ≤ Y → ‖F n s‖ ≤ M := by
    intro n Y
    obtain ⟨B, hB0, hB⟩ := bdd Φ a p hp1 hp hΦ (a - a') (by linarith)
    refine ⟨B, fun s hs _ => ?_⟩
    calc ‖F n s‖ = ‖Φ s‖ * ‖G a n s‖ := norm_mul _ _
      _ ≤ B * 1 := by
          gcongr
          · exact hB s (by linarith)
          · exact norm_G_le_one a n s (by linarith)
      _ = B := mul_one B
  have key : ∀ n, (1 / (2 * (Real.pi : ℂ) * I)) * (I * ∫ y : ℝ,
      F n ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z)) =
        if z.re < a' then F n z else 0 := by
    intro n
    have := (MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound).2 a a' (F n) ha'
      (hdiff n) (hsch n) (hchan n) z hz
    exact this.2
  -- passage to the limit `n → ∞`
  have hlimL : Tendsto (fun n => ∫ y : ℝ,
      F n ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z)) atTop
      (𝓝 (∫ y : ℝ, Φ ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖Φ ((a' : ℂ) + (y : ℂ) * I) / ((a' : ℂ) + (y : ℂ) * I - z)‖) (fun n => ?_)
      hint.norm (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · have hc1 := line_continuous Φ a hΦ.1 a' ha'
      have hc2 : Continuous (fun y : ℝ => G a n ((a' : ℂ) + (y : ℂ) * I)) := by
        refine continuous_iff_continuousAt.2 fun y => ?_
        have hl : Continuous (fun y : ℝ => (a' : ℂ) + (y : ℂ) * I) := by fun_prop
        have hG : ContinuousAt (G a n) ((a' : ℂ) + (y : ℂ) * I) :=
          (G_differentiableAt a n _ (by simpa using ha')).continuousAt
        exact ContinuousAt.comp (f := fun y : ℝ => (a' : ℂ) + (y : ℂ) * I) (x := y) hG hl.continuousAt
      exact ((hc1.mul hc2).div (by fun_prop) (fun y => ker_ne a' y z hz)).aestronglyMeasurable
    · simp only [hF, norm_div, norm_mul]
      have := norm_G_le_one a n ((a' : ℂ) + (y : ℂ) * I) (by simp; linarith)
      have h0 : 0 ≤ ‖Φ ((a' : ℂ) + (y : ℂ) * I)‖ / ‖(a' : ℂ) + (y : ℂ) * I - z‖ := by positivity
      rw [mul_div_right_comm]
      exact mul_le_of_le_one_right h0 this
    · have := (G_tendsto a ((a' : ℂ) + (y : ℂ) * I)).const_mul (Φ ((a' : ℂ) + (y : ℂ) * I))
      have := this.div_const ((a' : ℂ) + (y : ℂ) * I - z)
      simpa [hF] using this
  have hlimR : Tendsto (fun n => if z.re < a' then F n z else 0) atTop
      (𝓝 (if z.re < a' then Φ z else 0)) := by
    split_ifs with h
    · simpa [hF] using (G_tendsto a z).const_mul (Φ z)
    · exact tendsto_const_nhds
  have hlimL' := (hlimL.const_mul I).const_mul (1 / (2 * (Real.pi : ℂ) * I))
  have heq := tendsto_nhds_unique (hlimL'.congr key) hlimR
  rw [← heq, ← mul_assoc]
  congr 1
  have hI : (I:ℂ) ≠ 0 := I_ne_zero
  field_simp

/-! ### The boundary line `Re s = a` -/

theorem boundary (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y)))
    (z : ℂ) (hz : z.re ≠ a) :
    Integrable (fun y : ℝ => g y / ((a : ℂ) + (y : ℂ) * Complex.I - z)) volume ∧
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, g y / ((a : ℂ) + (y : ℂ) * Complex.I - z) =
        if z.re < a then Φ z else 0 := by
  have hq : p.HolderConjugate p.conjExponent := .conjExponent hp1
  have hq1 : 1 < p.conjExponent := one_lt_conjExponent hp1 hp
  set q := p.conjExponent with hq_def
  set δ := |a - z.re| with hδ_def
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))
  -- an approximating sequence `σₙ ↑ a`
  have hu : Tendsto (fun n : ℕ => a - 1 / ((n:ℝ) + 1)) atTop (𝓝[<] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := a)).sub this
    · have : 0 < 1 / ((n:ℝ) + 1) := by positivity
      simp only [Set.mem_Iio]
      linarith
  have hgm : AEStronglyMeasurable g volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n : ℕ => fun y : ℝ => Φ (((a - 1 / ((n:ℝ) + 1) : ℝ) : ℂ) + (y : ℂ) * I))
      (fun n => ?_) ?_
    · have : 0 < 1 / ((n:ℝ) + 1) := by positivity
      exact (line_continuous Φ a hΦ.1 _ (by linarith)).aestronglyMeasurable
    · filter_upwards [hg] with y hy using hy.comp hu
  -- `L^p` convergence of the vertical-line functions to the boundary function
  have hLp : Tendsto (fun σ : ℝ => eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y) p volume)
      (𝓝[<] a) (𝓝 0) :=
    HardyHalfPlane.tendsto_eLpNorm_sub_boundary_function Φ a p hp1 hp hΦ g hg
  have hgL : MemLp g p volume := by
    obtain ⟨σ₀, hσ₀, hσ₀a⟩ := ((hLp.eventually (gt_mem_nhds zero_lt_one)).and
      (self_mem_nhdsWithin : ∀ᶠ σ in 𝓝[<] a, σ < a)).exists
    have hd : MemLp (fun y : ℝ => Φ ((σ₀ : ℂ) + (y : ℂ) * I) - g y) p volume :=
      ⟨(line_continuous Φ a hΦ.1 σ₀ hσ₀a).aestronglyMeasurable.sub hgm,
        lt_trans hσ₀ ENNReal.one_lt_top⟩
    have := (line_memLp Φ a p hΦ σ₀ hσ₀a).sub hd
    have he : ((fun y : ℝ => Φ ((σ₀ : ℂ) + (y : ℂ) * I)) -
        fun y : ℝ => Φ ((σ₀ : ℂ) + (y : ℂ) * I) - g y) = g := by
      funext y; simp
    rwa [he] at this
  have hker : ∀ σ : ℝ, z.re ≠ σ → MemLp (fun y : ℝ => 1 / ((σ:ℂ) + (y:ℂ) * I - z)) q volume :=
    fun σ hσ => ker_memLp σ z hσ hq1
  have hint : Integrable (fun y : ℝ => g y / ((a : ℂ) + (y : ℂ) * I - z)) volume := by
    have := hgL.integrable_mul (hker a hz)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  refine ⟨hint, ?_⟩
  -- eventually `σ` is close to `a`
  have hnear : ∀ᶠ σ in 𝓝[<] a, σ < a ∧ |σ - a| ≤ δ / 2 := by
    have h1 : ∀ᶠ σ in 𝓝[<] a, σ < a := self_mem_nhdsWithin
    have h2 : ∀ᶠ σ in 𝓝 a, |σ - a| ≤ δ / 2 := by
      have : Metric.closedBall a (δ / 2) ∈ 𝓝 a := Metric.closedBall_mem_nhds a (by positivity)
      filter_upwards [this] with σ hσ
      rwa [Metric.mem_closedBall, Real.dist_eq] at hσ
    exact h1.and (h2.filter_mono nhdsWithin_le_nhds)
  have hzσ : ∀ σ : ℝ, |σ - a| ≤ δ / 2 → z.re ≠ σ := by
    intro σ hσ h
    rw [← h, abs_sub_comm] at hσ
    linarith
  -- the kernels
  set K : ℝ → ℝ → ℂ := fun σ y => 1 / ((σ:ℂ) + (y:ℂ) * I - z) with hK_def
  have hKle : ∀ σ : ℝ, |σ - a| ≤ δ / 2 → ∀ y, ‖K σ y‖ ≤ 2 * ‖K a y‖ := by
    intro σ hσ y
    simp only [hK_def, norm_div, norm_one]
    have h1 := norm_ker_le_two a σ y z hσ
    have h2 : 0 < ‖(σ:ℂ) + (y:ℂ) * I - z‖ := norm_pos_iff.mpr (ker_ne σ y z (hzσ σ hσ))
    have h3 : 0 < ‖(a:ℂ) + (y:ℂ) * I - z‖ := norm_pos_iff.mpr (ker_ne a y z hz)
    rw [div_le_iff₀ h2, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ h3]
    linarith
  have hT1 : Tendsto (fun σ : ℝ => ∫ y : ℝ, (Φ ((σ : ℂ) + (y : ℂ) * I) - g y) * K σ y)
      (𝓝[<] a) (𝓝 0) := by
    rw [tendsto_zero_iff_enorm_tendsto_zero]
    have hC : eLpNorm (K a) q volume ≠ ∞ := (hker a hz).2.ne
    have hbound : Tendsto (fun σ : ℝ => eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y)
        p volume * (2 * eLpNorm (K a) q volume)) (𝓝[<] a) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hLp
        (Or.inr (ENNReal.mul_ne_top (by norm_num : (2:ℝ≥0∞) ≠ ∞) hC))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hnear] with σ hσ
    obtain ⟨hσa, hσ⟩ := hσ
    have hKσm : AEStronglyMeasurable (K σ) volume :=
      (continuous_ker σ z (hzσ σ hσ)).aestronglyMeasurable
    have hdm : AEStronglyMeasurable (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y) volume :=
      (line_continuous Φ a hΦ.1 σ hσa).aestronglyMeasurable.sub hgm
    calc ‖∫ y : ℝ, (Φ ((σ : ℂ) + (y : ℂ) * I) - g y) * K σ y‖ₑ
        ≤ ∫⁻ y : ℝ, ‖(Φ ((σ : ℂ) + (y : ℂ) * I) - g y) * K σ y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = eLpNorm ((fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y) • K σ) 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm]; rfl
      _ ≤ eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y) p volume *
            eLpNorm (K σ) q volume :=
          eLpNorm_smul_le_mul_eLpNorm hKσm hdm
      _ ≤ eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y) p volume *
            (2 * eLpNorm (K a) q volume) := by
          gcongr
          have := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (p := q)
            (Eventually.of_forall (hKle σ hσ))
          simpa using this
  have hT2 : Tendsto (fun σ : ℝ => ∫ y : ℝ, g y * K σ y) (𝓝[<] a)
      (𝓝 (∫ y : ℝ, g y * K a y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => 2 * ‖g y * K a y‖) ?_ ?_ ?_ ?_
    · filter_upwards [hnear] with σ hσ
      exact hgm.mul (continuous_ker σ z (hzσ σ hσ.2)).aestronglyMeasurable
    · filter_upwards [hnear] with σ hσ
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul, norm_mul]
      have := hKle σ hσ.2 y
      nlinarith [norm_nonneg (g y)]
    · exact (hgL.integrable_mul (hker a hz)).norm.const_mul 2
    · refine Eventually.of_forall fun y => ?_
      have hc : ContinuousAt (fun σ : ℝ => g y * K σ y) a := by
        refine continuousAt_const.mul ?_
        simp only [hK_def]
        exact continuousAt_const.div (by fun_prop) (ker_ne a y z hz)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsplit : ∀ᶠ σ : ℝ in 𝓝[<] a,
      ∫ y : ℝ, Φ ((σ:ℂ) + (y:ℂ) * I) / ((σ:ℂ) + (y:ℂ) * I - z) =
      (∫ y : ℝ, (Φ ((σ : ℂ) + (y : ℂ) * I) - g y) * K σ y) + ∫ y : ℝ, g y * K σ y := by
    filter_upwards [hnear] with σ hσ
    obtain ⟨hσa, hσ⟩ := hσ
    have hKσ := hker σ (hzσ σ hσ)
    have hfL : MemLp (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I) - g y) p volume :=
      (line_memLp Φ a p hΦ σ hσa).sub hgL
    have h1 : Integrable (fun y : ℝ => (Φ ((σ : ℂ) + (y : ℂ) * I) - g y) * K σ y) volume :=
      hfL.integrable_mul hKσ
    have h2 : Integrable (fun y : ℝ => g y * K σ y) volume := hgL.integrable_mul hKσ
    rw [← integral_add h1 h2]
    congr 1
    funext y
    simp only [hK_def]
    ring
  have hlim : Tendsto (fun σ : ℝ => ∫ y : ℝ, Φ ((σ:ℂ) + (y:ℂ) * I) / ((σ:ℂ) + (y:ℂ) * I - z))
      (𝓝[<] a) (𝓝 (∫ y : ℝ, g y / ((a:ℂ) + (y:ℂ) * I - z))) := by
    have := hT1.add hT2
    rw [zero_add] at this
    have heqint : ∫ y : ℝ, g y * K a y = ∫ y : ℝ, g y / ((a:ℂ) + (y:ℂ) * I - z) := by
      congr 1; funext y; simp [hK_def, div_eq_mul_inv]
    rw [heqint] at this
    exact this.congr' (hsplit.mono fun σ h => h.symm)
  have hev : ∀ᶠ σ : ℝ in 𝓝[<] a, (1 / (2 * (Real.pi : ℂ))) *
      ∫ y : ℝ, Φ ((σ:ℂ) + (y:ℂ) * I) / ((σ:ℂ) + (y:ℂ) * I - z) =
        if z.re < a then Φ z else 0 := by
    filter_upwards [hnear] with σ hσ
    obtain ⟨hσa, hσ⟩ := hσ
    rw [(interior Φ a p hp1 hp hΦ σ hσa z (hzσ σ hσ)).2]
    have hiff : z.re < σ ↔ z.re < a := by
      constructor
      · intro h; linarith
      · intro h
        have h1 : δ = a - z.re := by rw [hδ_def, abs_of_pos (by linarith)]
        have h2 := (abs_le.mp hσ).1
        linarith
    simp only [hiff]
  exact tendsto_nhds_unique (hlim.const_mul _)
    (tendsto_const_nhds.congr' (hev.mono fun σ h => h.symm))

end Sol_HardyHalfPlane_cauchy_integral_formula

open Sol_HardyHalfPlane_cauchy_integral_formula in
theorem solution (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : HardyHalfPlane.MemLeftHardy Φ a p) (a' : ℝ) (ha' : a' ≤ a) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a') (𝓝 (g y)))
    (z : ℂ) (hz : z.re ≠ a') :
    Integrable (fun y : ℝ => g y / ((a' : ℂ) + (y : ℂ) * Complex.I - z)) volume ∧
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, g y / ((a' : ℂ) + (y : ℂ) * Complex.I - z) =
        if z.re < a' then Φ z else 0 := by
  rcases lt_or_eq_of_le ha' with hlt | heq
  · have hae : ∀ᵐ y : ℝ ∂volume, g y = Φ ((a' : ℂ) + (y : ℂ) * Complex.I) := by
      filter_upwards [hg] with y hy
      have hc : ContinuousAt (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) a' := by
        have h1 : ContinuousAt Φ ((a' : ℂ) + (y : ℂ) * Complex.I) :=
          hΦ.1.continuousOn.continuousAt
            ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simpa using hlt))
        have hl : Continuous (fun σ : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
        exact ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I) (x := a')
          h1 hl.continuousAt
      exact tendsto_nhds_unique hy (hc.tendsto.mono_left nhdsWithin_le_nhds)
    have hae' : (fun y : ℝ => g y / ((a' : ℂ) + (y : ℂ) * Complex.I - z)) =ᵐ[volume]
        fun y : ℝ => Φ ((a' : ℂ) + (y : ℂ) * Complex.I) / ((a' : ℂ) + (y : ℂ) * Complex.I - z) :=
      hae.mono fun y hy => by simp only [hy]
    obtain ⟨h1, h2⟩ := interior Φ a p hp1 hp hΦ a' hlt z hz
    exact ⟨h1.congr hae'.symm, by rw [integral_congr_ae hae', h2]⟩
  · subst heq
    exact boundary Φ _ p hp1 hp hΦ g hg z hz
