-- Prove2me | solution 1 for HadamardLaplacePublished.real_heat_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:09:31.877628+00:00
-- url     : https://prove2.me/submissions/973f874f-a342-472c-9b96-3c271924b5f9

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
namespace LaplaceBridge

theorem real_gamma_nat (r : ℕ) (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t^r * Real.exp (-(a*t))) =
      (r.factorial : ℝ) * (a⁻¹)^(r+1) := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((r+1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  rw [show ((r+1 : ℕ) : ℝ)-1 = (r : ℝ) by push_cast; ring] at hg
  simp only [Real.rpow_natCast] at hg
  rw [show Real.Gamma ((r+1 : ℕ) : ℝ) = (r.factorial : ℝ) by
      simpa using Real.Gamma_nat_eq_factorial r] at hg
  simpa only [one_div, mul_comm] using hg

theorem real_weight_integrable (r : ℕ) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t^r * Real.exp (-(a*t))) (Ioi 0) := by
  by_contra h
  have hv := real_gamma_nat r a ha
  rw [integral_undef h] at hv
  have hp : 0 < (r.factorial : ℝ) * (a⁻¹)^(r+1) := by positivity
  linarith

theorem complex_weight_integrable (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^r * Complex.exp (-(a*t))) (Ioi 0) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  apply (real_weight_integrable r a.re ha).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [Complex.norm_exp, Complex.mul_re, abs_of_pos (mem_Ioi.mp ht)]

theorem integral_complex_weight_norm (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ)^r * Complex.exp (-(a*t))‖) =
      (r.factorial : ℝ) * (a.re⁻¹)^(r+1) := by
  rw [← real_gamma_nat r a.re ha]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp [Complex.norm_exp, Complex.mul_re, abs_of_pos (mem_Ioi.mp ht)]

theorem complex_weight_tendsto_zero (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => (t : ℂ)^r * Complex.exp (-(a*t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (r : ℝ) a.re ha
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp [Real.rpow_natCast, Complex.norm_exp, Complex.mul_re, abs_of_pos ht]

theorem complex_weight_derivative (r : ℕ) (a : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)^(r+1)*Complex.exp (-(a*t)))
      (((r+1 : ℕ) : ℂ)*((t : ℂ)^r*Complex.exp (-(a*t))) -
        a*((t : ℂ)^(r+1)*Complex.exp (-(a*t)))) t := by
  have hp := (hasDerivAt_id (t : ℂ)).pow (r+1)
  have he := (Complex.hasDerivAt_exp _).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (-a))
  have hd := (hp.mul he).comp_ofReal
  convert! hd using 1 <;> simp [neg_mul, pow_succ] <;> ring

theorem complex_gamma_nat (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)^r*Complex.exp (-(a*t))) =
      (r.factorial : ℂ) * (a⁻¹)^(r+1) := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  induction r with
  | zero =>
    simpa [neg_mul] using integral_exp_mul_complex_Ioi (a := -a) (by simpa) 0
  | succ r ih =>
    have hi := (complex_weight_integrable r a ha).const_mul (((r+1 : ℕ) : ℂ))
    have hj := (complex_weight_integrable (r+1) a ha).const_mul a
    have hf := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun t (_ : t ∈ Ici (0 : ℝ)) => complex_weight_derivative r a t)
      (hi.sub hj) (complex_weight_tendsto_zero (r+1) a ha)
    rw [integral_sub hi hj, integral_const_mul, integral_const_mul] at hf
    simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero r), zero_mul,
      sub_zero] at hf
    apply (mul_left_cancel₀ ha0)
    calc
      a * (∫ t : ℝ in Ioi 0, (t : ℂ)^(r+1)*Complex.exp (-(a*t))) =
          ((r+1 : ℕ) : ℂ) * (∫ t : ℝ in Ioi 0, (t : ℂ)^r*Complex.exp (-(a*t))) :=
        (sub_eq_zero.mp hf).symm
      _ = a * ((↑(r+1).factorial : ℂ) * a⁻¹^((r+1)+1)) := by
        rw [ih, Nat.factorial_succ]
        push_cast
        simp only [pow_succ]
        field_simp

theorem weighted_norm_integrals_summable (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun i => ∫ t : ℝ in Ioi 0,
      ‖(t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))‖) := by
  have hpos : ∀ i, 0 < ((x : ℂ)+B i).re := by
    intro i
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hB i]
  simp_rw [integral_complex_weight_norm r _ (hpos _)]
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (inv_nonneg.mpr (hpos i).le) _)) _ (hs.mul_left (r.factorial : ℝ))
  intro i
  have hb : 0 < (B i).re := by linarith [hB i]
  have ha : 0 < x+(B i).re := by linarith
  have hi : (x+(B i).re)⁻¹ ≤ (B i).re⁻¹ := (inv_le_inv₀ ha hb).2 (by linarith)
  have hi1 : (x+(B i).re)⁻¹ ≤ 1 := (inv_le_one₀ ha).2 (by linarith [hB i])
  have hip : 0 ≤ (x+(B i).re)⁻¹ := by positivity
  have hp : ((x+(B i).re)⁻¹)^(r+1) ≤ (B i).re⁻¹ := by
    rw [pow_succ]
    have hh : ((x+(B i).re)⁻¹)^r * (x+(B i).re)⁻¹ ≤ (x+(B i).re)⁻¹ := by
      simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hip hi1 :
        ((x+(B i).re)⁻¹)^r ≤ 1) hip
    exact hh.trans hi
  simpa only [Complex.add_re, Complex.ofReal_re] using
    mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg r.factorial)

theorem laplace_series_identity (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, ∑' i,
      (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))) =
      (r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1) := by
  have hpos : ∀ i, 0 < ((x : ℂ)+B i).re := by
    intro i
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hB i]
  rw [← integral_tsum_of_summable_integral_norm
    (fun i => complex_weight_integrable r _ (hpos i))
    (weighted_norm_integrals_summable B r hB hs x hx)]
  simp_rw [complex_gamma_nat r _ (hpos _)]
  exact tsum_mul_left

theorem laplace_series_integrable (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => ∑' i,
      (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))) (Ioi 0) := by
  let F : ℕ → ℝ → ℂ := fun i t => (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hi : ∀ i, Integrable (F i) μ := by
    intro i
    apply complex_weight_integrable
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hB i]
  have hsum : Summable (fun i => ∫ t, ‖F i t‖ ∂μ) :=
    weighted_norm_integrals_summable B r hB hs x hx
  have he (i : ℕ) : ∫⁻ t, ‖F i t‖ₑ ∂μ = ‖∫ t, ‖F i t‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F i t)))]
    simp only [coe_nnnorm]
  have hfin : (∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ) < ⊤ := by
    simp_rw [he]
    exact (ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hsum.abs)).lt_top
  change Integrable (fun t => ∑' i, F i t) μ
  refine ⟨?_, ?_⟩
  · apply Measurable.aestronglyMeasurable
    exact Measurable.tsum (fun i => by dsimp [F]; fun_prop)
  · rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ t, ‖∑' i, F i t‖ₑ ∂μ) ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ ∂μ :=
        lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
      _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ := lintegral_tsum (fun i => (hi i).1.enorm)
      _ < ⊤ := hfin

theorem heat_series_summable (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (t : ℝ) (ht : 0 < t) : Summable (fun i => Complex.exp (-(B i*t))) := by
  apply (hs.mul_left t⁻¹).of_norm_bounded
  intro i
  have hb : 0 < (B i).re := by linarith [hB i]
  have hp : 0 < (B i).re*t := mul_pos hb ht
  have hle : (B i).re*t ≤ Real.exp ((B i).re*t) := by
    linarith [Real.add_one_le_exp ((B i).re*t)]
  simp only [Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Real.exp_neg]
  calc
    (Real.exp ((B i).re*t))⁻¹ ≤ ((B i).re*t)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) hp).2 hle
    _ = t⁻¹ * (B i).re⁻¹ := by rw [mul_inv_rev]

theorem real_heat_integrand_eq (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x t : ℝ) (ht : 0 < t) :
    (∑' i, (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t))).re =
      t^r * Real.exp (-(x*t)) * ∑' i, (Complex.exp (-(B i*t))).re := by
  have he (i : ℕ) : (t : ℂ)^r * Complex.exp (-(((x : ℂ)+B i)*t)) =
      ((t : ℂ)^r * Complex.exp (-((x : ℂ)*t))) * Complex.exp (-(B i*t)) := by
    rw [show -(((x : ℂ)+B i)*t) = -((x : ℂ)*t) + -(B i*t) by ring,
      Complex.exp_add]
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  have hc : ((t : ℂ)^r * Complex.exp (-((x : ℂ)*t))) =
      ((t^r * Real.exp (-(x*t)) : ℝ) : ℂ) := by
    norm_cast
  rw [hc, Complex.re_ofReal_mul]
  congr 1
  exact Complex.reCLM.map_tsum (heat_series_summable B hB hs t ht)

theorem real_heat_integral_identity (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) =
      ((r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re := by
  rw [← laplace_series_identity B r hB hs x hx]
  have hr := integral_re (laplace_series_integrable B r hB hs x hx)
  simp only [RCLike.re_to_complex] at hr
  rw [← hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (real_heat_integrand_eq B r hB hs x t (mem_Ioi.mp ht)).symm

theorem real_heat_integrable (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) (Ioi 0) := by
  apply (laplace_series_integrable B r hB hs x hx).re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact real_heat_integrand_eq B r hB hs x t (mem_Ioi.mp ht)

end LaplaceBridge

theorem solution (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) (Ioi 0) ∧
    ((∫ t : ℝ in Ioi 0, t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) =
      ((r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re) := by
  exact ⟨LaplaceBridge.real_heat_integrable B r hB hs x hx,
    LaplaceBridge.real_heat_integral_identity B r hB hs x hx⟩
