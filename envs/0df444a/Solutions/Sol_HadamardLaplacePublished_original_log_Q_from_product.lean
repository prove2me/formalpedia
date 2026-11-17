-- Prove2me | solution 1 for HadamardLaplacePublished.original_log_Q_from_product
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:09:40.911447+00:00
-- url     : https://prove2.me/submissions/a23d4110-fb04-4826-8c88-8ae925680886

import Mathlib

open scoped BigOperators
open Set Filter Topology
noncomputable section
namespace HadamardSeries

def domain : Set ℂ := {z | -(1/2 : ℝ) < z.re}

theorem domain_open : IsOpen domain :=
  isOpen_lt continuous_const Complex.continuous_re

theorem domain_convex : Convex ℝ domain := by
  intro x hx y hy a b ha hb hab
  change -(1/2 : ℝ) < (a • x + b • y).re
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  change -(1/2 : ℝ) < x.re at hx
  change -(1/2 : ℝ) < y.re at hy
  by_cases h : a = 0
  · subst a
    have hbb : b = 1 := by linarith
    simpa [hbb] using hy
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    nlinarith [mul_pos hap (show 0 < x.re+1/2 by linarith),
      mul_nonneg hb (show 0 ≤ y.re+1/2 by linarith)]

theorem zero_mem : (0 : ℂ) ∈ domain := by norm_num [domain]

theorem realpart_pos (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    0 < (z+B).re := by
  change -(1/2 : ℝ) < z.re at hz
  simp only [Complex.add_re]
  linarith

theorem denominator_nonzero (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    z+B ≠ 0 := by
  have hp := realpart_pos B z hB hz
  intro h
  simp [h] at hp

theorem inverse_bound (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    ‖(z+B)⁻¹‖ ≤ 2 * B.re⁻¹ := by
  have hb : 0 < B.re := by linarith
  have hd : B.re/2 ≤ ‖z+B‖ := by
    have hr := Complex.re_le_norm (z+B)
    change -(1/2 : ℝ) < z.re at hz
    simp only [Complex.add_re] at hr
    linarith
  rw [norm_inv]
  calc
    ‖z+B‖⁻¹ ≤ (B.re/2)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0 < B.re/2) hd) (by positivity)).2 hd
    _ = 2 * B.re⁻¹ := by field_simp

theorem inverse_power_bound (B z : ℂ) (r : ℕ)
    (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    ‖((z+B)⁻¹)^(r+1)‖ ≤ 2^(r+1) * B.re⁻¹ := by
  have hb : 0 ≤ B.re⁻¹ := inv_nonneg.mpr (by linarith)
  have hle : B.re⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hB
  have hp : (B.re⁻¹)^r ≤ 1 := pow_le_one₀ hb hle
  rw [norm_pow]
  calc
    ‖(z+B)⁻¹‖^(r+1) ≤ (2*B.re⁻¹)^(r+1) :=
      pow_le_pow_left₀ (norm_nonneg _) (inverse_bound B z hB hz) _
    _ = 2^(r+1) * ((B.re⁻¹)^r * B.re⁻¹) := by rw [mul_pow, pow_succ (B.re⁻¹)]
    _ ≤ 2^(r+1) * B.re⁻¹ := mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul_of_nonneg_right hp hb) (by positivity)

theorem pole_power_summable (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    Summable (fun i => ((z+B i)⁻¹)^(r+1)) := by
  exact (hs.mul_left (2^(r+1))).of_norm_bounded
    (fun i => inverse_power_bound (B i) z r (hB i) hz)

theorem log_atom_derivative (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    HasDerivAt (fun w => Complex.log (w+B) - Complex.log B) ((z+B)⁻¹) z := by
  have hd := (Complex.hasDerivAt_log (by
    exact Or.inl (realpart_pos B z hB hz))).comp z ((hasDerivAt_id z).add_const B)
  simpa using hd.sub_const (Complex.log B)

theorem log_series_derivative (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∑' i, (Complex.log (w+B i) - Complex.log (B i)))
      (∑' i, (z+B i)⁻¹) z := by
  apply hasDerivAt_tsum_of_isPreconnected (hs.mul_left 2)
    domain_open domain_convex.isPreconnected
    (fun i w hw => log_atom_derivative (B i) w (hB i) hw)
    (fun i w hw => inverse_bound (B i) w (hB i) hw) zero_mem
  · simp
  · exact hz

theorem log_series_summable (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    Summable (fun i => Complex.log (z+B i) - Complex.log (B i)) := by
  apply summable_of_summable_hasDerivAt_of_isPreconnected (hs.mul_left 2)
    domain_open domain_convex.isPreconnected
    (fun i w hw => log_atom_derivative (B i) w (hB i) hw)
    (fun i w hw => inverse_bound (B i) w (hB i) hw) zero_mem
  · simp
  · exact hz

theorem canonical_product_hasProd (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasProd (fun i => 1+z/B i)
      (Complex.exp (∑' i, (Complex.log (z+B i) - Complex.log (B i)))) := by
  have hsum := (log_series_summable B hB hs z hz).hasSum
  have ht := (Complex.continuous_exp.tendsto _).comp hsum
  have hterm : ∀ i, Complex.exp (Complex.log (z+B i) - Complex.log (B i)) = 1+z/B i := by
    intro i
    have hb : B i ≠ 0 := by
      have := hB i
      intro he
      norm_num [he] at this
    rw [Complex.exp_sub, Complex.exp_log (denominator_nonzero _ _ (hB i) hz),
      Complex.exp_log hb]
    field_simp
    ring
  simpa only [HasProd, Function.comp_def, Complex.exp_sum, hterm] using ht

theorem canonical_product_eq_exp (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    (∏' i, (1+z/B i)) =
      Complex.exp (∑' i, (Complex.log (z+B i) - Complex.log (B i))) :=
  (canonical_product_hasProd B hB hs z hz).tprod_eq

theorem canonical_product_derivative (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∏' i, (1+w/B i))
      ((∏' i, (1+z/B i)) * ∑' i, (z+B i)⁻¹) z := by
  have hd := (Complex.hasDerivAt_exp _).comp z (log_series_derivative B hB hs z hz)
  rw [← canonical_product_eq_exp B hB hs z hz] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [domain_open.mem_nhds hz] with w hw
  exact canonical_product_eq_exp B hB hs w hw

theorem pole_atom_derivative (B z : ℂ) (r : ℕ)
    (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    HasDerivAt (fun w => ((w+B)⁻¹)^(r+1))
      (-((r+1 : ℕ) : ℂ) * ((z+B)⁻¹)^(r+2)) z := by
  have hd := (((hasDerivAt_id z).add_const B).inv
    (denominator_nonzero B z hB hz)).pow (r+1)
  convert! hd using 1 <;>
    simp [Nat.add_sub_cancel, one_div, div_eq_mul_inv, inv_pow, pow_succ] <;> ring

theorem pole_series_derivative (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∑' i, ((w+B i)⁻¹)^(r+1))
      (-((r+1 : ℕ) : ℂ) * ∑' i, ((z+B i)⁻¹)^(r+2)) z := by
  have hbound : ∀ i w, w ∈ domain →
      ‖-((r+1 : ℕ) : ℂ) * ((w+B i)⁻¹)^(r+2)‖ ≤
        ((r+1 : ℕ) : ℝ) * 2^(r+2) * (B i).re⁻¹ := by
    intro i w hw
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (inverse_power_bound (B i) w (r+1) (hB i) hw) (Nat.cast_nonneg _)
  have hd := hasDerivAt_tsum_of_isPreconnected
    (hs.mul_left (((r+1 : ℕ) : ℝ)*2^(r+2))) domain_open domain_convex.isPreconnected
    (fun i w hw => pole_atom_derivative (B i) w r (hB i) hw) hbound
    zero_mem (pole_power_summable B r hB hs 0 zero_mem) hz
  simpa only [tsum_mul_left] using hd

theorem log_series_iteratedDeriv (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (z : ℂ) (hz : z ∈ domain) :
    iteratedDeriv (r+1) (fun w => ∑' i,
      (Complex.log (w+B i) - Complex.log (B i))) z =
      (-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, ((z+B i)⁻¹)^(r+1) := by
  induction r generalizing z with
  | zero =>
    simpa using (log_series_derivative B hB hs z hz).deriv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (r+1) (fun w => ∑' i,
        (Complex.log (w+B i) - Complex.log (B i))) =ᶠ[𝓝 z]
        (fun w => (-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, ((w+B i)⁻¹)^(r+1)) := by
      filter_upwards [domain_open.mem_nhds hz] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    rw [((pole_series_derivative B r hB hs z hz).const_mul
      ((-1 : ℂ)^r * (r.factorial : ℂ))).deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

end HadamardSeries


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

namespace CanonicalQBridge

theorem real_log_iteratedDeriv (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (x : ℝ) (hx : -(1/2 : ℝ) < x) :
    iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
      (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) x =
      ((-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re := by
  have hz : (x : ℂ) ∈ HadamardSeries.domain := hx
  induction r generalizing x with
  | zero =>
    have hd := (HadamardSeries.log_series_derivative B hB hs (x : ℂ) hz).comp_ofReal
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    simpa [Function.comp_def] using hr.deriv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
        (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) =ᶠ[𝓝 x]
        (fun v : ℝ => ((-1 : ℂ)^r*(r.factorial : ℂ)*
          ∑' i, (((v : ℂ)+B i)⁻¹)^(r+1)).re) := by
      filter_upwards [Ioi_mem_nhds hx] with v hv
      exact ih v hv hv
    rw [he.deriv_eq]
    have hd := ((HadamardSeries.pole_series_derivative B r hB hs (x : ℂ) hz).const_mul
      ((-1 : ℂ)^r*(r.factorial : ℂ))).comp_ofReal
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    have hh := hr.deriv
    change deriv (fun v : ℝ => ((-1 : ℂ)^r*(r.factorial : ℂ)*
      ∑' i, (((v : ℂ)+B i)⁻¹)^(r+1)).re) x = _ at hh
    rw [hh]
    change (_ : ℂ).re = (_ : ℂ).re
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem derivative_equals_heat_integral (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (-1 : ℝ)^r * iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
      (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) x =
    ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re := by
  rw [real_log_iteratedDeriv B hB hs r x (by linarith),
    LaplaceBridge.real_heat_integral_identity B r hB hs x hx]
  have hc : (-1 : ℂ)^r*(r.factorial : ℂ) =
      (((-1 : ℝ)^r*(r.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.re_ofReal_mul]
  rw [show (r.factorial : ℂ) = ((r.factorial : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul]
  have hsign : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ)^r * (-1 : ℝ)^r) *
      ((r.factorial : ℝ) * (∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem normalized_Q_integral (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
        (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) (u^2) =
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1) *
      ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(u^2*t)) *
        ∑' i, (Complex.exp (-(B i*t))).re := by
  rw [mul_assoc ((2 : ℝ)^(r+1)*u^(2*(r+1)-1)),
    derivative_equals_heat_integral B hB hs r (u^2) (sq_nonneg u)]

theorem positive_function_log_identity (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) (hg : 0 < g x)
    (hp : (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i)) :
    Real.log (g x) - Real.log c =
      (∑' i, (Complex.log ((x : ℂ)+B i) - Complex.log (B i))).re := by
  have hz : (x : ℂ) ∈ HadamardSeries.domain := by
    change -(1/2 : ℝ) < x
    linarith
  rw [HadamardSeries.canonical_product_eq_exp B hB hs (x : ℂ) hz] at hp
  have hn := congrArg (fun z : ℂ => Real.log ‖z‖) hp
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hg hc), abs_of_pos hg, abs_of_pos hc,
    Complex.norm_exp, Real.log_exp, Real.log_div (ne_of_gt hg) (ne_of_gt hc)] using hn

theorem original_log_Q_from_product (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) =
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1) *
      ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(u^2*t)) *
        ∑' i, (Complex.exp (-(B i*t))).re := by
  have he : (fun x => Real.log (g x) - Real.log c) =ᶠ[𝓝 (u^2)]
      (fun x : ℝ => (∑' i,
        (Complex.log ((x : ℂ)+B i) - Complex.log (B i))).re) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos hu)] with x hx
    exact positive_function_log_identity B hB hs g c x hc hx (hg x hx) (hp x hx)
  rw [he.iteratedDeriv_eq (r+1)]
  exact normalized_Q_integral B hB hs r u hu

end CanonicalQBridge


theorem solution (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) =
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1) *
      ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(u^2*t)) *
        ∑' i, (Complex.exp (-(B i*t))).re := by
  exact CanonicalQBridge.original_log_Q_from_product B hB hs g c hc hg hp r u hu
