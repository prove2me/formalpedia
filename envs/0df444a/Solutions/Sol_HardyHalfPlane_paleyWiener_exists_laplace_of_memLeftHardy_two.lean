-- Prove2me | solution 1 for HardyHalfPlane.paleyWiener_exists_laplace_of_memLeftHardy_two
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:25:17.602941+00:00
-- url     : https://prove2.me/submissions/7491f217-ff49-4fd0-bd5a-c51f4acf4cef

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy
import Theorems.Thm_MasulloGRH_asymptotic_cauchy_value_formula_with_channel_bound

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace Sol_HardyHalfPlane_paleyWiener_exists_laplace_of_memLeftHardy_two

open Filter Topology

/-! ## Part 1. The Cauchy integral formula on interior vertical lines

For `Φ ∈ H^p(ℂ_{<a})`, `1 ≤ p < ∞`, and `a' < a`, the Cauchy integral over the line `Re s = a'`
reproduces `Φ` to the left of the line. Deduced from the platform theorem
`MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound` (part 2) applied to `Φ · G_n`,
where `G_n` is a regulariser with fast vertical decay, and dominated convergence. -/

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

/-! ## Part 2. Plancherel and the Laplace representation -/

namespace PW

open Complex
open scoped FourierTransform SchwartzMap InnerProductSpace

theorem ae_eq_of_schwartz_pairing {f : ℝ → ℂ} (hf : Continuous f)
    {u : Lp ℂ 2 (volume : Measure ℝ)}
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, φ t * f t) = ∫ t, φ t * u t) :
    f =ᵐ[volume] (u : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable
    ((Lp.memLp u).locallyIntegrable one_le_two)
  intro g hg hc
  let gC : ℝ → ℂ := ofRealCLM ∘ g
  have hcC : HasCompactSupport gC := hc.comp_left rfl
  let φ := hcC.toSchwartzMap (ofRealCLM.contDiff.comp hg)
  exact h φ

theorem fourier_ae {g : ℝ → ℂ} (h₁ : Integrable g) (h₂ : MemLp g 2) :
    𝓕 g =ᵐ[volume] (𝓕 (h₂.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) := by
  have hcont (L : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) (hL : Continuous fun p : ℝ × ℝ ↦ L p.1 p.2) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hL h₁
  apply ae_eq_of_schwartz_pairing (hcont _ continuous_inner)
  intro φ
  have hd := congrArg (fun D : 𝓢'(ℝ, ℂ) ↦ D φ) (Lp.fourier_toTemperedDistribution_eq (h₂.toLp g))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  rw [← hd]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner h₁ φ.integrable
  rw [flip_innerₗ] at h
  simp only [smul_eq_mul] at h
  calc
    _ = ∫ t, (𝓕 g) t * φ t := by simp_rw [mul_comm (φ _)]; rfl
    _ = ∫ t, g t * 𝓕 (φ : ℝ → ℂ) t := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with t ht
      rw [ht, mul_comm, SchwartzMap.fourier_coe]

theorem pairing (ψ : ℝ → ℂ) (hψ : MemLp ψ 2) :
    ∃ H : ℝ → ℂ, MemLp H 2 volume ∧ eLpNorm H 2 volume = eLpNorm ψ 2 volume ∧
      ∀ κ : ℝ → ℂ, Integrable κ → MemLp κ 2 →
        ∫ ξ, ψ ξ * 𝓕 κ ξ = ∫ x, H x * κ x := by
  have hψc : MemLp (star ψ) 2 volume := hψ.star
  set A : Lp ℂ 2 (volume : Measure ℝ) := hψc.toLp (star ψ) with hA
  set B : Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ A with hB
  refine ⟨star (B : ℝ → ℂ), (Lp.memLp B).star, ?_, ?_⟩
  · have h1 : eLpNorm (star (B : ℝ → ℂ)) 2 volume = eLpNorm (B : ℝ → ℂ) 2 volume :=
      eLpNorm_star
    have h2 : eLpNorm ψ 2 volume = eLpNorm (A : ℝ → ℂ) 2 volume := by
      rw [eLpNorm_congr_ae hψc.coeFn_toLp]
      exact eLpNorm_star.symm
    have hFB : 𝓕 B = A := by simp [hB]
    have h3 : ‖B‖ = ‖A‖ := by
      rw [← hFB, Lp.norm_fourier_eq]
    have h4 : ‖B‖ₑ = ‖A‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      congr 1
      exact NNReal.eq h3
    rw [h1, h2, ← Lp.enorm_def, ← Lp.enorm_def]
    exact h4
  · intro κ hκ1 hκ2
    set K : Lp ℂ 2 (volume : Measure ℝ) := hκ2.toLp κ
    have hF := fourier_ae hκ1 hκ2
    have hinner : ⟪𝓕 B, 𝓕 K⟫_ℂ = ⟪B, K⟫_ℂ := Lp.inner_fourier_eq B K
    have hFB : 𝓕 B = A := by simp [hB]
    rw [hFB] at hinner
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hinner
    have eL : ∫ ξ, ψ ξ * 𝓕 κ ξ = ∫ a, ⟪(A : ℝ → ℂ) a, (𝓕 K : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [hF, hψc.coeFn_toLp] with ξ h1 h2
      rw [h1, h2]
      simp [RCLike.inner_apply, K, mul_comm]
    have eR : ∫ x, star (B : ℝ → ℂ) x * κ x = ∫ a, ⟪(B : ℝ → ℂ) a, (K : ℝ → ℂ) a⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [hκ2.coeFn_toLp] with x h1
      rw [h1]
      simp [RCLike.inner_apply, mul_comm]
    rw [eL, eR, hinner]

/-- The one-sided exponential `x ↦ 1_{x>0} e^{w x}`. -/
noncomputable def kexp (w : ℂ) : ℝ → ℂ := Set.indicator (Set.Ioi 0) (fun x : ℝ => cexp (w * x))

lemma kexp_integrable (w : ℂ) (hw : w.re < 0) : Integrable (kexp w) :=
  (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_exp_mul_complex_Ioi hw 0)

lemma norm_kexp_le (w : ℂ) (hw : w.re < 0) (x : ℝ) : ‖kexp w x‖ ≤ 1 := by
  unfold kexp
  by_cases hx : x ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem hx, Complex.norm_exp]
    have : (w * (x:ℂ)).re = w.re * x := by simp
    rw [this, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hw.le (le_of_lt hx)
  · rw [Set.indicator_of_notMem hx]; simp

lemma kexp_memLp (w : ℂ) (hw : w.re < 0) : MemLp (kexp w) 2 := by
  have hm : AEStronglyMeasurable (kexp w) volume := (kexp_integrable w hw).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine (kexp_integrable w hw).norm.mono' (hm.norm.pow 2) (Eventually.of_forall fun x => ?_)
  have h1 := norm_kexp_le w hw x
  have h0 := norm_nonneg (kexp w x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

lemma exp_mul_kexp (a w : ℂ) (x : ℝ) : cexp (a * x) * kexp w x = kexp (w + a) x := by
  unfold kexp
  by_cases hx : x ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ← Complex.exp_add]
    ring_nf
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

lemma fourier_kexp (w : ℂ) (hw : w.re < 0) (ξ : ℝ) :
    𝓕 (kexp w) ξ = 1 / (2 * (Real.pi : ℂ) * (ξ : ℂ) * I - w) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h1 : (fun v : ℝ => cexp (↑(-2 * Real.pi * v * ξ) * I) • kexp w v) =
      kexp (w + (-2 * (Real.pi : ℂ) * (ξ : ℂ) * I)) := by
    funext v
    rw [smul_eq_mul, ← exp_mul_kexp]
    congr 2
    push_cast
    ring
  rw [h1]
  set a : ℂ := w + (-2 * (Real.pi : ℂ) * (ξ : ℂ) * I) with ha
  have hare : a.re < 0 := by simp [ha]; exact hw
  unfold kexp
  rw [integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hare 0]
  have hne : a ≠ 0 := fun h => by rw [h] at hare; simp at hare
  have hne' : 2 * (Real.pi : ℂ) * (ξ : ℂ) * I - w ≠ 0 := by
    intro h; apply hne; rw [ha]; linear_combination -h
  field_simp
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [ha]; ring

/-- Injectivity of the Fourier transform on `L¹ ∩ L²`. -/
theorem uniq (u : ℝ → ℂ) (h1 : Integrable u) (h2 : MemLp u 2) (h : ∀ ξ, 𝓕 u ξ = 0) :
    u =ᵐ[volume] 0 := by
  have hF := fourier_ae h1 h2
  have h0 : 𝓕 (h2.toLp u) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hF] with ξ hξ
    rw [← hξ, h ξ]; rfl
  have h3 : h2.toLp u = 0 := by
    rw [← norm_eq_zero, ← Lp.norm_fourier_eq, h0, norm_zero]
  have h4 := h2.coeFn_toLp
  rw [h3] at h4
  filter_upwards [h4, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hx0
  rw [← hx, hx0]

/-- On each vertical line `Re s = σ < 0`, `Φ` is the Laplace transform of an `L²` function, with
uniformly bounded norm. -/
theorem line_repr (Φ : ℂ → ℂ) (hΦ : HardyHalfPlane.MemLeftHardy Φ 0 2) (σ : ℝ) (hσ : σ < 0) :
    ∃ H : ℝ → ℂ, MemLp H 2 volume ∧
      eLpNorm H 2 volume ≤ HardyHalfPlane.leftHardyNorm Φ 0 2 ∧
      ∀ z : ℂ, z.re < σ → Φ z = ∫ x, H x * kexp (z - σ) x := by
  set φ : ℝ → ℂ := fun y => Φ ((σ:ℂ) + (y:ℂ) * I) with hφ
  have hφc : Continuous φ := line_continuous Φ 0 hΦ.1 σ hσ
  have hφL : MemLp φ 2 volume := line_memLp Φ 0 2 hΦ σ hσ
  have hφb : eLpNorm φ 2 volume ≤ HardyHalfPlane.leftHardyNorm Φ 0 2 := by
    unfold HardyHalfPlane.leftHardyNorm
    exact le_iSup₂ (f := fun σ (_ : σ < (0:ℝ)) =>
      eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) 2 volume) σ hσ
  set c : ℝ := 2 * Real.pi with hc
  have hc0 : 0 < c := by positivity
  have hc1 : 1 ≤ c := by rw [hc]; linarith [Real.pi_gt_three]
  set ψ : ℝ → ℂ := fun ξ => φ (c * ξ) with hψ
  have hmap : Measure.map (fun ξ : ℝ => c * ξ) volume = ENNReal.ofReal |c⁻¹| • volume :=
    Real.map_volume_mul_left hc0.ne'
  have hψeq : eLpNorm ψ 2 volume =
      ENNReal.ofReal |c⁻¹| ^ (1 / (2:ℝ≥0∞)).toReal • eLpNorm φ 2 volume := by
    have := eLpNorm_map_measure (p := 2) (g := φ) (f := fun ξ : ℝ => c * ξ) (μ := volume)
      hφc.aestronglyMeasurable (by fun_prop)
    show eLpNorm (φ ∘ fun ξ : ℝ => c * ξ) 2 volume = _
    rw [← this, hmap, eLpNorm_smul_measure_of_ne_top (by norm_num)]
  have hk : ENNReal.ofReal |c⁻¹| ^ (1 / (2:ℝ≥0∞)).toReal ≤ 1 := by
    apply ENNReal.rpow_le_one _ ENNReal.toReal_nonneg
    apply ENNReal.ofReal_le_one.2
    rw [abs_inv, abs_of_pos hc0]
    exact inv_le_one_of_one_le₀ hc1
  have hψb : eLpNorm ψ 2 volume ≤ eLpNorm φ 2 volume := by
    rw [hψeq, smul_eq_mul]
    calc _ ≤ 1 * eLpNorm φ 2 volume := by gcongr
      _ = _ := one_mul _
  have hψL : MemLp ψ 2 volume :=
    ⟨(hφc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable,
      lt_of_le_of_lt hψb hφL.2⟩
  obtain ⟨H, hHL, hHn, hHp⟩ := pairing ψ hψL
  refine ⟨H, hHL, by rw [hHn]; exact hψb.trans hφb, fun z hz => ?_⟩
  have hw : (z - (σ:ℂ)).re < 0 := by simp; linarith
  have hcf := (interior Φ 0 2 (by norm_num) (by norm_num) hΦ σ hσ z (ne_of_lt hz)).2
  rw [if_pos hz] at hcf
  set g : ℝ → ℂ := fun y : ℝ => Φ ((σ:ℂ) + (y:ℂ) * I) / ((σ:ℂ) + (y:ℂ) * I - z) with hg
  have key : ∫ ξ, ψ ξ * 𝓕 (kexp (z - σ)) ξ = (1 / (2 * (Real.pi:ℂ))) * ∫ y : ℝ, g y := by
    have h1 : (fun ξ => ψ ξ * 𝓕 (kexp (z - σ)) ξ) = fun ξ => g (c * ξ) := by
      funext ξ
      rw [fourier_kexp _ hw]
      simp only [hψ, hφ, hg]
      rw [mul_one_div]
      congr 1
      rw [hc]
      push_cast
      ring
    rw [h1, Measure.integral_comp_mul_left g c, abs_of_pos (inv_pos.2 hc0), Complex.real_smul, hc]
    push_cast
    ring
  rw [← hcf, ← key, hHp (kexp (z - σ)) (kexp_integrable _ hw) (kexp_memLp _ hw)]

theorem main (Φ : ℂ → ℂ) (hΦ : HardyHalfPlane.MemLeftHardy Φ 0 2) :
    ∃ f : ℝ → ℂ, MemLp f 2 volume ∧ (∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) ∧
      ∀ s : ℂ, s.re < 0 → Φ s = ∫ x : ℝ, f x * Complex.exp (s * x) := by
  set σ : ℕ → ℝ := fun n => -(1 / ((n:ℝ) + 1)) with hσdef
  have hσneg : ∀ n, σ n < 0 := fun n => by
    have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    simp only [hσdef]; linarith
  have hσge : ∀ n, -1 ≤ σ n := fun n => by
    have : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    simp only [hσdef]; linarith
  have hσlim : Tendsto σ atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := h0.neg
    rw [neg_zero] at this
    exact this
  choose H hHL hHb hHr using fun n => line_repr Φ hΦ (σ n) (hσneg n)
  set L := HardyHalfPlane.leftHardyNorm Φ 0 2 with hL
  set G : ℕ → ℝ → ℂ := fun n x => H n x * cexp (-(σ n : ℂ) * x) with hG
  -- uniqueness of the representing function
  have huniq : ∀ n, ∀ᵐ x : ℝ ∂volume, 0 < x → G n x = G 0 x := by
    intro n
    set c : ℝ := -2 with hc
    have hw : ∀ m, ((c:ℂ) - σ m).re < 0 := fun m => by simp [hc]; linarith [hσge m]
    have hint : ∀ m (w : ℂ), w.re < 0 → Integrable (fun x => H m x * kexp w x) :=
      fun m w hw => (hHL m).integrable_mul (kexp_memLp w hw)
    have hmemL : ∀ m, MemLp (fun x => H m x * kexp (c - σ m) x) 2 := fun m =>
      (hHL m).of_le ((hHL m).1.mul (kexp_integrable _ (hw m)).1) (Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_kexp_le _ (hw m) x))
    set u : ℝ → ℂ := fun x => H n x * kexp (c - σ n) x - H 0 x * kexp (c - σ 0) x with hu
    have hu1 : Integrable u := (hint n _ (hw n)).sub (hint 0 _ (hw 0))
    have hu2 : MemLp u 2 := (hmemL n).sub (hmemL 0)
    have hFu : ∀ ξ, 𝓕 u ξ = 0 := by
      intro ξ
      set z : ℂ := (c:ℂ) - 2 * (Real.pi:ℂ) * (ξ:ℂ) * I with hz
      have hzre : ∀ m, z.re < σ m := fun m => by simp [hz, hc]; linarith [hσge m]
      have hzw : ∀ m, (z - σ m).re < 0 := fun m => by
        have := hzre m; simp only [Complex.sub_re, Complex.ofReal_re]; linarith
      have hpt : (fun v : ℝ => cexp (↑(-2 * Real.pi * v * ξ) * I) • u v) =
          fun v => H n v * kexp (z - σ n) v - H 0 v * kexp (z - σ 0) v := by
        funext v
        have he : cexp (↑(-2 * Real.pi * v * ξ) * I) =
            cexp ((-2 * (Real.pi:ℂ) * (ξ:ℂ) * I) * (v:ℂ)) := by
          congr 1; push_cast; ring
        simp only [hu, smul_eq_mul, mul_sub, he]
        rw [mul_left_comm, exp_mul_kexp, mul_left_comm, exp_mul_kexp]
        have e1 : ∀ m, (c:ℂ) - σ m + (-2 * (Real.pi:ℂ) * (ξ:ℂ) * I) = z - σ m := fun m => by
          rw [hz]; ring
        rw [e1, e1]
      rw [Real.fourier_real_eq_integral_exp_smul, hpt,
        integral_sub (hint n _ (hzw n)) (hint 0 _ (hzw 0)), ← hHr n z (hzre n),
        ← hHr 0 z (hzre 0), sub_self]
    have hae := uniq u hu1 hu2 hFu
    filter_upwards [hae] with x hx hx0
    have h1 : H n x * kexp (c - σ n) x = H 0 x * kexp (c - σ 0) x := sub_eq_zero.1 hx
    simp only [kexp, Set.indicator_of_mem (show x ∈ Set.Ioi (0:ℝ) from hx0)] at h1
    have e : ∀ m, G m x = H m x * cexp (((c:ℂ) - σ m) * x) * cexp (-(c:ℂ) * x) := fun m => by
      simp only [hG]; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
    rw [e n, e 0, h1]
  -- the candidate
  set f : ℝ → ℂ := Set.indicator (Set.Ioi 0) (G 0) with hf
  have hGm : ∀ n, AEStronglyMeasurable (G n) volume := fun n =>
    (hHL n).1.mul (by fun_prop : Continuous fun x : ℝ => cexp (-(σ n : ℂ) * x)).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f volume := (hGm 0).indicator measurableSet_Ioi
  set F : ℕ → ℝ → ℂ := fun n x => f x * cexp ((σ n : ℂ) * x) with hF
  have hFm : ∀ n, AEStronglyMeasurable (F n) volume := fun n =>
    hfm.mul (by fun_prop : Continuous fun x : ℝ => cexp ((σ n : ℂ) * x)).aestronglyMeasurable
  have hFlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    intro x
    have hc : Continuous fun t : ℝ => cexp ((t : ℂ) * x) := by fun_prop
    have := ((hc.tendsto 0).comp hσlim).const_mul (f x)
    simpa [hF] using this
  have hFb : ∀ n, eLpNorm (F n) 2 volume ≤ L := by
    intro n
    refine le_trans (eLpNorm_mono_ae ?_) (hHb n)
    filter_upwards [huniq n] with x hx
    by_cases hx0 : 0 < x
    · have : F n x = H n x := by
        simp only [hF, hf, Set.indicator_of_mem (show x ∈ Set.Ioi (0:ℝ) from hx0)]
        rw [← hx hx0, hG]
        simp only
        rw [mul_assoc, ← Complex.exp_add]
        simp
      rw [this]
    · have : F n x = 0 := by
        simp [hF, hf, Set.indicator_of_notMem (show x ∉ Set.Ioi (0:ℝ) from hx0)]
      rw [this, norm_zero]; exact norm_nonneg _
  have hfb : eLpNorm f 2 volume ≤ L :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm hFm f (Eventually.of_forall hFlim)).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hFb))
  refine ⟨f, ⟨hfm, lt_of_le_of_lt hfb hΦ.2⟩, Eventually.of_forall fun x hx =>
    Set.indicator_of_notMem (show x ∉ Set.Ioi (0:ℝ) by simp; linarith) _, fun s hs => ?_⟩
  obtain ⟨n, hn⟩ := (hσlim.eventually (lt_mem_nhds hs)).exists
  rw [hHr n s hn]
  apply integral_congr_ae
  filter_upwards [huniq n] with x hx
  by_cases hx0 : 0 < x
  · simp only [kexp, hf, Set.indicator_of_mem (show x ∈ Set.Ioi (0:ℝ) from hx0)]
    rw [← hx hx0, hG]
    simp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · simp [kexp, hf, Set.indicator_of_notMem (show x ∉ Set.Ioi (0:ℝ) from hx0)]

end PW

end Sol_HardyHalfPlane_paleyWiener_exists_laplace_of_memLeftHardy_two

theorem solution (Φ : ℂ → ℂ)
    (hΦ : HardyHalfPlane.MemLeftHardy Φ 0 2) :
    ∃ f : ℝ → ℂ, MemLp f 2 volume ∧ (∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) ∧
      ∀ s : ℂ, s.re < 0 → Φ s = ∫ x : ℝ, f x * Complex.exp (s * x) :=
  Sol_HardyHalfPlane_paleyWiener_exists_laplace_of_memLeftHardy_two.PW.main Φ hΦ
