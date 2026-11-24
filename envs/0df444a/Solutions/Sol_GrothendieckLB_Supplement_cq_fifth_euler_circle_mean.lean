-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_fifth_euler_circle_mean
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:10:36.55173+00:00
-- url     : https://prove2.me/submissions/86d2ad3f-f7c9-4db8-a0b4-dbe1526b9cc7

import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_euler_quarter_bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Complex.TaylorSeries

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement Filter MeasureTheory
open scoped Topology Matrix ENNReal NNReal

open scoped Interval Real
set_option maxHeartbeats 1500000
namespace CQCircle
private theorem allowable_extension {ρ : ℝ → ℝ} (hρ : IsAllowableCorr ρ) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖φ z‖ ≤ ‖z‖) ∧
      (∀ x : ℝ, |x| < 1 → φ x = (ρ x : ℂ)) := by
  obtain ⟨c, he, hs, hmass, heq⟩ := hρ
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))
  have hrad : (1 : ℝ≥0∞) ≤ p.radius := by
    have h := p.le_radius_of_summable_norm (r := (1 : ℝ≥0)) (by
      simpa [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hs)
    simpa using h
  have hrepr (z : ℂ) : p.sum z = ∑' n, (c n : ℂ) * z^n :=
    FormalMultilinearSeries.ofScalars_sum_eq (fun n => (c n : ℂ)) z
  refine ⟨p.sum, ?_, ?_, ?_⟩
  · intro z hz
    apply (p.analyticOnNhd z ?_).differentiableAt.differentiableWithinAt
    apply Metric.eball_subset_eball hrad
    change z ∈ Metric.eball (0 : ℂ) ((1 : ℝ≥0) : ℝ≥0∞)
    rw [Metric.eball_coe]
    exact hz
  · intro z hz
    rw [hrepr]
    apply le_trans (tsum_of_norm_bounded (hs.hasSum.mul_right ‖z‖) ?_)
      (mul_le_of_le_one_left (norm_nonneg _) hmass)
    intro n
    cases n with
    | zero => simp [he 0 (by decide)]
    | succ n =>
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_succ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg z) (pow_le_one₀ (norm_nonneg z) hz.le)) (abs_nonneg _)
  · intro x hx
    rw [hrepr, heq x hx, Complex.ofReal_tsum]
    exact tsum_congr fun n => by push_cast; ring

private noncomputable def gaussPref (w : ℂ) : ℂ :=
  (1 - w^2) ^ ((-(1/2 : ℝ) : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ)

private noncomputable def gaussKernel (w : ℂ) (x y : ℝ) : ℂ :=
  gaussPref w * Complex.exp (-(
    ((((x+y)^2/4 : ℝ) : ℂ) * (1+w)⁻¹) +
    ((((x-y)^2/4 : ℝ) : ℂ) * (1-w)⁻¹)))

private theorem gaussian_factors {w : ℂ} (hw : ‖w‖ < 1) :
    (1+w ≠ 0) ∧ (1-w ≠ 0) ∧ 1-w^2 ∈ Complex.slitPlane := by
  have ht : |w.re| < 1 := (Complex.abs_re_le_norm w).trans_lt hw
  have hre₁ : 0 < (1+w).re := by simp; linarith [(abs_lt.mp ht).1]
  have hre₂ : 0 < (1-w).re := by simp; linarith [(abs_lt.mp ht).2]
  refine ⟨fun h => by rw [h] at hre₁; simpa using hre₁,
    fun h => by rw [h] at hre₂; simpa using hre₂, ?_⟩
  rw [sub_eq_add_neg]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_neg, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hw (by decide)

private theorem pref_diff {w : ℂ} (hw : ‖w‖ < 1) : DifferentiableAt ℂ gaussPref w := by
  have hslit := (gaussian_factors hw).2.2
  have hd : DifferentiableAt ℂ (fun z : ℂ => 1-z^2) w := by fun_prop
  unfold gaussPref
  exact (hd.cpow_const hslit).div_const _

private theorem kernel_diff {w : ℂ} (hw : ‖w‖ < 1) (x y : ℝ) :
    DifferentiableAt ℂ (fun z => gaussKernel z x y) w := by
  obtain ⟨h₁, h₂, _⟩ := gaussian_factors hw
  unfold gaussKernel
  apply (pref_diff hw).mul
  fun_prop (disch := assumption)

private theorem kernel_real {t : ℝ} (ht : |t| < 1) (x y : ℝ) :
    gaussKernel t x y =
      (((1 / (2 * Real.pi * Real.sqrt (1-t^2))) *
        Real.exp (-(x^2 - 2*t*x*y + y^2)/(2*(1-t^2))) : ℝ) : ℂ) := by
  have h₁ : 0 < 1+t := by linarith [(abs_lt.mp ht).1]
  have h₂ : 0 < 1-t := by linarith [(abs_lt.mp ht).2]
  have hsq : 0 < 1-t^2 := by nlinarith [mul_pos h₁ h₂]
  have hpre : gaussPref t = ((1/(2 * Real.pi * Real.sqrt (1-t^2)) : ℝ) : ℂ) := by
    unfold gaussPref
    rw [show (1 : ℂ) - (t : ℂ)^2 = ((1-t^2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hsq.le, Real.rpow_neg hsq.le, ← Real.sqrt_eq_rpow]
    push_cast
    ring
  have har : -(((x+y)^2/4)*(1+t)⁻¹ + ((x-y)^2/4)*(1-t)⁻¹) =
      -(x^2 - 2*t*x*y + y^2)/(2*(1-t^2)) := by
    field_simp [h₁.ne',h₂.ne',hsq.ne'] <;> ring
  unfold gaussKernel
  rw [hpre, Complex.ofReal_mul]
  congr 1
  rw [← har]
  push_cast
  ring

private theorem inv_re_lower {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    (1-R)/(1+R)^2 ≤ ((1+w)⁻¹).re := by
  have h₁ : 1-R ≤ (1+w).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h₂ : ‖1+w‖ ≤ 1+R := by
    calc
      _ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 1 + R := by rw [norm_one]; linarith
  have hn := (gaussian_factors (hw.trans_lt hR1)).1
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  apply div_le_div₀ ((sub_nonneg.mpr hR1.le).trans h₁) h₁ (sq_pos_of_pos (norm_pos_iff.mpr hn))
  exact pow_le_pow_left₀ (norm_nonneg _) h₂ 2

private theorem kernel_bound (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ (w : ℂ), ‖w‖ ≤ R → ∀ x y : ℝ, ‖gaussKernel w x y‖ ≤
        C * (Real.exp (-a*x^2) * Real.exp (-a*y^2)) := by
  have hcont : ContinuousOn (fun w : ℂ => ‖gaussPref w‖) (Metric.closedBall 0 R) := by
    intro w hw
    exact (pref_diff ((by simpa using hw : ‖w‖ ≤ R).trans_lt hR1)).continuousAt.norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hcont
  let D := (1-R)/(1+R)^2
  have hD : 0 < D := div_pos (sub_pos.mpr hR1) (by positivity)
  refine ⟨max C 0, D/2, le_max_right _ _, by positivity, ?_⟩
  intro w hw x y
  have hpre : ‖gaussPref w‖ ≤ max C 0 :=
    (hC (Set.mem_image_of_mem _ (show w ∈ Metric.closedBall 0 R by simpa using hw))).trans
      (le_max_left _ _)
  have hplus : D ≤ ((1+w)⁻¹).re := inv_re_lower hR hR1 hw
  have hminus : D ≤ ((1-w)⁻¹).re := by
    simpa only [D, sub_eq_add_neg] using
      (inv_re_lower hR hR1 (show ‖-w‖ ≤ R by rwa [norm_neg]))
  rw [gaussKernel, norm_mul, Complex.norm_exp, ← Real.exp_add]
  apply mul_le_mul hpre _ (Real.exp_pos _).le (le_max_right _ _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.neg_re, Complex.add_re, Complex.re_ofReal_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hplus (sq_nonneg (x+y)),
    mul_le_mul_of_nonneg_left hminus (sq_nonneg (x-y))]

private theorem differentiable_dominated_disk {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : ℂ → X → ℂ) (hm : ∀ z, Measurable (K z))
    (hh : ∀ x, DifferentiableOn ℂ (fun z => K z x) (Metric.ball 0 1))
    (hmajor : ∀ R : ℝ, 0 ≤ R → R < 1 →
      ∃ B : X → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x, ‖K z x‖ ≤ B x) :
    DifferentiableOn ℂ (fun z => ∫ x, K z x ∂μ) (Metric.ball 0 1) := by
  intro z₀ hz₀
  have hz : ‖z₀‖ < 1 := by simpa using hz₀
  let e := (1-‖z₀‖)/4
  have he : 0 < e := by dsimp [e]; linarith
  let R := ‖z₀‖ + 2*e
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by dsimp [R,e]; linarith
  obtain ⟨B, hB, hb⟩ := hmajor R hR hR1
  have hKint : Integrable (K z₀) μ :=
    hB.mono' (hm _).aestronglyMeasurable (Filter.Eventually.of_forall (hb _ (by dsimp [R]; linarith)))
  let K' (z : ℂ) (x : X) := deriv (fun w => K w x) z
  have hmeas : AEStronglyMeasurable (K' z₀) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z₀)
      (f := fun w x => slope (fun z => K z x) z₀ w)
    · intro w
      simp only [slope_def_field]
      exact ((hm w).sub (hm z₀) |>.div_const _).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x =>
        hasDerivAt_iff_tendsto_slope.mp ((hh x).differentiableAt (Metric.isOpen_ball.mem_nhds hz₀)).hasDerivAt
  have hrad {z w : ℂ} (hz' : z ∈ Metric.ball z₀ e) (hw : w ∈ Metric.closedBall z e) :
      ‖w‖ ≤ R := by
    have h₁ : dist z z₀ < e := hz'
    have h₂ : dist w z ≤ e := hw
    have ht := dist_triangle w z z₀
    have ht' := dist_triangle w z₀ 0
    simp only [dist_zero_right] at ht'
    dsimp [R]
    linarith
  have hsub {z : ℂ} (hz' : z ∈ Metric.ball z₀ e) :
      Metric.closedBall z e ⊆ Metric.ball 0 1 := by
    intro w hw
    simpa using (hrad hz' hw).trans_lt hR1
  have hder (x : X) (z : ℂ) (hz' : z ∈ Metric.ball z₀ e) : ‖K' z x‖ ≤ B x / e :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le he ((hh x).diffContOnCl_ball (hsub hz'))
      (fun w hw => hb w (hrad hz' (Metric.sphere_subset_closedBall hw)) x)
  have hh' (x : X) (z : ℂ) (hz' : z ∈ Metric.ball z₀ e) : HasDerivAt (fun w => K w x) (K' z x) z :=
    ((hh x).differentiableAt (Metric.isOpen_ball.mem_nhds
      (hsub hz' (Metric.mem_closedBall_self he.le)))).hasDerivAt
  have hdi := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := K) (F' := K')
    (Metric.ball_mem_nhds z₀ he) (Filter.Eventually.of_forall fun w => (hm w).aestronglyMeasurable)
    hKint hmeas (Filter.Eventually.of_forall hder) (hB.div_const _) (Filter.Eventually.of_forall hh')
  exact hdi.2.differentiableAt.differentiableWithinAt

private theorem limiting_holomorphic {k : ℕ} (S : LimitingScheme k) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      ∀ t : ℝ, |t| < 1 → F t = (S.corr t : ℂ) := by
  classical
  choose φ hφ hb hreal using fun i => allowable_extension (S.ρ_allowable i)
  let X := Fin k → ℝ
  let K (z : ℂ) (p : X × X) : ℂ := ((S.f p.1 * S.g p.2 : ℝ) : ℂ) *
      ∏ i, gaussKernel (φ i z) (p.1 i) (p.2 i)
  have hm (z : ℂ) : Measurable (K z) := by
    dsimp only [K]
    apply (Complex.measurable_ofReal.comp ((S.measurable_f.comp measurable_fst).mul
      (S.measurable_g.comp measurable_snd))).mul
    apply Finset.measurable_prod
    intro i _
    unfold gaussKernel
    fun_prop
  have hh (p : X × X) : DifferentiableOn ℂ (fun z => K z p) (Metric.ball 0 1) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_mul
    have hd (i : Fin k) :
        DifferentiableAt ℂ (fun y => gaussKernel (φ i y) (p.1 i) (p.2 i)) z :=
      (kernel_diff ((hb i z hz').trans_lt hz') _ _).comp z
        ((hφ i).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
    exact DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hmajor (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
      ∃ B : X × X → ℝ, Integrable B volume ∧
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ p, ‖K z p‖ ≤ B p := by
    obtain ⟨C, a, hC, ha, hk⟩ := kernel_bound R hR hR1
    let q (x : X) := ∏ i, Real.exp (-a*(x i)^2)
    have hi : Integrable q (volume : Measure X) :=
      Integrable.fintype_prod fun _ : Fin k => integrable_exp_neg_mul_sq ha
    refine ⟨fun p => C^k * (q p.1 * q p.2), (hi.mul_prod hi).const_mul _, ?_⟩
    intro z hz p
    have hp : ‖((S.f p.1 * S.g p.2 : ℝ) : ℂ)‖ = 1 := by
      rcases S.f_sign p.1 with h|h <;> rcases S.g_sign p.2 with h'|h' <;> simp [h,h']
    simp only [K, norm_mul, hp, one_mul, norm_prod]
    calc
      _ ≤ ∏ i : Fin k, C*(Real.exp (-a*(p.1 i)^2)*Real.exp (-a*(p.2 i)^2)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
          hk _ ((hb i z (hz.trans_lt hR1)).trans hz) _ _
      _ = _ := by simp [q, Finset.prod_mul_distrib]
  refine ⟨fun z => ((Real.pi/2 : ℝ) : ℂ) * ∫ p, K z p,
    (differentiable_dominated_disk K hm hh hmajor).const_mul _, ?_⟩
  intro t ht
  have htc : ‖(t:ℂ)‖ < 1 := by simpa [Real.norm_eq_abs] using ht
  have hρ (i : Fin k) : |S.ρ i t| < 1 := by
    have h := hb i (t:ℂ) htc
    rw [hreal i t ht] at h
    simpa [Real.norm_eq_abs] using h.trans_lt htc
  obtain ⟨B, hB, hdom⟩ := hmajor ‖(t:ℂ)‖ (norm_nonneg _) htc
  have hI : Integrable (K (t:ℂ)) volume :=
    hB.mono' (hm _).aestronglyMeasurable (Filter.Eventually.of_forall (hdom _ le_rfl))
  change ((Real.pi/2 : ℝ) : ℂ) * (∫ p, K (t:ℂ) p) = _
  rw [Measure.volume_eq_prod, integral_prod _ (show Integrable _ (volume.prod volume) from hI)]
  change ((Real.pi/2 : ℝ) : ℂ) * _ = ((Real.pi/2 * ∫ x : X, ∫ y : X, _) : ℝ)
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with y
  simp only [K, fun i => hreal i t ht, fun i => kernel_real (hρ i), gaussianPairDensity, Fin.prod_univ_one]
  push_cast
  rfl

private noncomputable def E (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z

private lemma euler_analytic {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1)) (k : ℕ) :
    AnalyticOnNhd ℂ (E^[k] F) (Metric.ball 0 1) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro z hz
    exact analyticAt_id.mul (ih.deriv z hz)

private noncomputable def angle (s : ℝ) := 2*Real.arctan (s^2)
private noncomputable def jac (s : ℝ) := 4*s/(1+s^4)
private def bounds (s v : ℝ) : Prop :=
  (s ≤ 1/4 → v ≤ 531000) ∧ (1/4 ≤ s → s ≤ 1/2 → v ≤ 545000) ∧
  (1/2 ≤ s → s ≤ 3/4 → v ≤ 486000) ∧ (3/4 ≤ s → v ≤ 84000)

private lemma jac_cont : Continuous jac := by
  unfold jac
  exact (continuous_const.mul continuous_id).div (continuous_const.add (continuous_id.pow 4))
    (fun s => by positivity)

private lemma angle_deriv (s : ℝ) : HasDerivAt angle (jac s) s := by
  have hh := (((Real.hasDerivAt_arctan (s^2)).comp s ((hasDerivAt_id s).pow 2)).const_mul (2:ℝ))
  have h : 2 * ((1/(1+(s^2)^2)) * (↑(2:ℕ) * (id s)^(2-1:ℕ) * 1)) = jac s := by
    dsimp [jac]
    rw [show (s^2)^2=s^4 by ring]
    field_simp <;> ring
  simpa only [angle,Function.comp_apply,Pi.pow_apply,id_eq] using! hh.congr_deriv h
private lemma at_one : angle 1 = π/2 := by
  simp [angle,Real.arctan_one]; ring
private lemma at_zero : angle 0=0 := by simp [angle]

private lemma substitute_fifth {g f : ℝ → ℝ} (hg : Continuous g) (hf : Continuous f)
    (H : ∀ s ∈ Set.Icc 0 1, bounds s ((2/π*jac s)*g (f s))) :
    (∫ s in (0:ℝ)..1, g (f s)*jac s) ≤ π/2*416000 := by
  let J (s : ℝ) := g (f s)*jac s
  have hj : Continuous J := (hg.comp hf).mul jac_cont
  have bound (a b K : ℝ) (h : a ≤ b)
      (upper : ∀ s ∈ Set.Icc a b, (2/π*jac s)*g (f s) ≤ K) :
      (∫ s in a..b, J s) ≤ (b-a)*(π/2*K) := by
    calc
      _ ≤ ∫ _ in a..b, π/2*K := by
        apply intervalIntegral.integral_mono_on h (hj.intervalIntegrable _ _) (intervalIntegrable_const)
        intro s hs
        calc
          J s = (π/2)*((2/π*jac s)*g (f s)) := by dsimp [J]; field_simp [Real.pi_ne_zero]
          _ ≤ _ := mul_le_mul_of_nonneg_left (upper s hs) (by positivity)
      _ = _ := by simp [intervalIntegral.integral_const,smul_eq_mul] <;> ring
  have h1 := bound 0 (1/4) 531000 (by norm_num) (fun s hs =>
    (H s ⟨hs.1,by linarith only [hs.2]⟩).1 hs.2)
  have h2 := bound (1/4) (1/2) 545000 (by norm_num) (fun s hs =>
    (H s ⟨by linarith only [hs.1],by linarith only [hs.2]⟩).2.1 hs.1 hs.2)
  have h3 := bound (1/2) (3/4) 486000 (by norm_num) (fun s hs =>
    (H s ⟨by linarith only [hs.1],by linarith only [hs.2]⟩).2.2.1 hs.1 hs.2)
  have h4 := bound (3/4) 1 84000 (by norm_num) (fun s hs =>
    (H s ⟨by linarith only [hs.1],hs.2⟩).2.2.2 hs.1)
  have h := add_le_add (add_le_add h1 h2) (add_le_add h3 h4)
  rw [intervalIntegral.integral_add_adjacent_intervals (hj.intervalIntegrable _ _) (hj.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hj.intervalIntegrable _ _) (hj.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hj.intervalIntegrable _ _) (hj.intervalIntegrable _ _)] at h
  change (∫ s in (0:ℝ)..1,J s) ≤ _
  linarith only [h,Real.pi_pos]

private lemma forward_fifth {g : ℝ → ℝ} (hg : Continuous g) (a : ℝ)
    (h : ∀ s ∈ Set.Icc 0 1, bounds s ((2/π*jac s)*g (a+angle s))) :
    (∫ θ in a..a+π/2, g θ) ≤ π/2*416000 := by
  let f (s : ℝ) := a+angle s
  have hf : Continuous f := continuous_const.add (continuous_iff_continuousAt.mpr fun x => (angle_deriv x).continuousAt)
  have hd (s : ℝ) : HasDerivAt f (jac s) s := (angle_deriv s).const_add a
  have eq := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=1) (f:=f) (f':=jac)
    (fun s _ => hd s) jac_cont.continuousOn hg
  have hs := substitute_fifth (f:=f) hg hf h
  change (∫ s in (0:ℝ)..1, g (f s)*jac s) = ∫ θ in f 0..f 1, g θ at eq
  rw [eq] at hs
  simpa [f,at_zero,at_one] using hs

private lemma backward_fifth {g : ℝ → ℝ} (hg : Continuous g) (a : ℝ)
    (h : ∀ s ∈ Set.Icc 0 1, bounds s ((2/π*jac s)*g (a-angle s))) :
    (∫ θ in a-π/2..a, g θ) ≤ π/2*416000 := by
  let f (s : ℝ) := a-angle s
  have hf : Continuous f := continuous_const.sub (continuous_iff_continuousAt.mpr fun x => (angle_deriv x).continuousAt)
  have hd (s : ℝ) : HasDerivAt f (-(jac s)) s := by
    simpa only [f,Pi.sub_def,zero_sub] using! (hasDerivAt_const s a).sub (angle_deriv s)
  have eq := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=1) (f:=f) (f':=fun s => -(jac s))
    (fun s _ => hd s) jac_cont.neg.continuousOn hg
  change (∫ s in (0:ℝ)..1, g (f s)*(-jac s)) = ∫ θ in f 0..f 1, g θ at eq
  simp only [mul_neg,intervalIntegral.integral_neg] at eq
  have eq' : (∫ s in (0:ℝ)..1, g (f s)*jac s) = ∫ θ in f 1..f 0, g θ := by
    rw [intervalIntegral.integral_symm (a:=f 0) (b:=f 1)]
    linarith only [eq]
  have hs := substitute_fifth (f:=f) hg hf h
  rw [eq'] at hs
  simpa [f,at_zero,at_one] using hs

private lemma assemble (g : ℝ → ℝ) (hg : Continuous g)
    (h : ∀ s ∈ Set.Icc 0 1, ∀ θ : ℝ, (let a := angle s
        θ = a ∨ θ = π-a ∨ θ = π+a ∨ θ = 2*π-a) → bounds s ((2/π*jac s)*g θ)) :
    (2*π)⁻¹*(∫ θ in 0..2*π, g θ) ≤ 416000 := by
  have h₁ := forward_fifth hg 0 (fun s hs => h s hs _ (.inl (zero_add _)))
  have h₂ := backward_fifth hg π (fun s hs => h s hs _ (.inr (.inl rfl)))
  have h₃ := forward_fifth hg π (fun s hs => h s hs _ (.inr (.inr (.inl rfl))))
  have h₄ := backward_fifth hg (2*π) (fun s hs => h s hs _ (.inr (.inr (.inr rfl))))
  rw [zero_add] at h₁
  rw [show π - π/2 = π/2 by ring] at h₂
  rw [show 2*π - π/2 = π+π/2 by ring] at h₄
  have hs := add_le_add (add_le_add h₁ h₂) (add_le_add h₃ h₄)
  rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)] at hs
  rw [← div_eq_inv_mul, div_le_iff₀ (by positivity : 0 < 2*π)]
  linarith only [hs,Real.pi_pos]

end CQCircle
open CQCircle

theorem solution :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      (∀ t : ℝ, |t| < 1 → F (t : ℂ) = (cqCorr 0.136419125 0.34101124 0.05276111 t : ℂ)) ∧
      (∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1),
        Real.circleAverage (fun z : ℂ =>
          ‖(((fun g : ℂ → ℂ => fun w : ℂ => w * deriv g w)^[5]) F) z‖) 0 r ≤ 416000) := by
  obtain ⟨S,hS⟩ := exists_limitingScheme_cqCorr 0.136419125 0.34101124 0.05276111
  obtain ⟨F,hF,hrl⟩ := limiting_holomorphic S
  rw [hS] at hrl
  refine ⟨F,hF,hrl,?_⟩
  have hrad : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), (99999:ℝ)/100000 < r :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (99999:ℝ)/100000 < 1))
  have hr₁ : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), r < 1 := self_mem_nhdsWithin
  filter_upwards [hrad,hr₁] with r hr hr'
  let G := E^[5] F
  let g (θ : ℝ) := ‖G (circleMap 0 r θ)‖
  have hG := euler_analytic (hF.analyticOnNhd Metric.isOpen_ball) 5
  have hc : Continuous g := (hG.continuousOn.comp_continuous (continuous_circleMap 0 r) (fun θ => by
    have hrp : 0 < r := by linarith
    simpa [Metric.mem_ball,dist_zero_right,norm_circleMap_zero,abs_of_pos hrp] using hr')).norm
  change (2*π)⁻¹*(∫ θ in 0..2*π, g θ) ≤ 416000
  apply assemble g hc
  intro s hs θ hθ
  exact cq_fifth_euler_quarter_bounds F hF hrl r s θ hr.le hr' hs hθ
