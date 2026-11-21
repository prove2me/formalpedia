-- Prove2me | solution 2 for MasulloRH.regularized_spectral_domination
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:24:39.416023+00:00
-- url     : https://prove2.me/submissions/5656cf43-5606-4088-8398-6c984bedcde9

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

private noncomputable abbrev sTr : ℝ → ℝ := Real.smoothTransition
private noncomputable def d1 : ℝ → ℝ := deriv sTr
private noncomputable def d2 : ℝ → ℝ := deriv d1

private lemma st_smooth : ContDiff ℝ ∞ sTr := Real.smoothTransition.contDiff (n := ⊤)

private lemma d1_smooth : ContDiff ℝ ∞ d1 := (contDiff_infty_iff_deriv.1 st_smooth).2

private lemma st_hasDeriv (x : ℝ) : HasDerivAt sTr (d1 x) x :=
  ((contDiff_infty_iff_deriv.1 st_smooth).1 x).hasDerivAt

private lemma d1_hasDeriv (x : ℝ) : HasDerivAt d1 (d2 x) x :=
  ((contDiff_infty_iff_deriv.1 d1_smooth).1 x).hasDerivAt

private lemma d1_cont : Continuous d1 := d1_smooth.continuous

private lemma d2_cont : Continuous d2 :=
  (contDiff_infty_iff_deriv.1 d1_smooth).2.continuous

private lemma d1_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : d1 x = 0 := by
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; exact hx ⟨le_rfl, zero_le_one⟩) with h | h
  · have : sTr =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simp [d1, this.deriv_eq]
  · have h1 : 1 < x := by
      by_contra h'; exact hx ⟨h.le, not_lt.1 h'⟩
    have : sTr =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simp [d1, this.deriv_eq]

private lemma d2_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : d2 x = 0 := by
  have hopen : IsOpen (Icc (0 : ℝ) 1)ᶜ := isClosed_Icc.isOpen_compl
  have : d1 =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact d1_zero hy
  simp [d2, this.deriv_eq]

private lemma d1_cs : HasCompactSupport d1 :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => d1_zero hx)

private lemma d2_cs : HasCompactSupport d2 :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => d2_zero hx)

private noncomputable def hw (f : ℝ → ℝ) (v : ℝ) : ℝ := |f v| * (|v| + 1)

private lemma hw_nonneg (f : ℝ → ℝ) (v : ℝ) : 0 ≤ hw f v := by
  unfold hw; positivity

private lemma hw_int (f : ℝ → ℝ) (hc : Continuous f) (hs : HasCompactSupport f) :
    Integrable (hw f) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold hw; fun_prop
  · exact (hs.abs).mul_right

/-- Substitution bound. -/
private lemma comp_bound (h : ℝ → ℝ) (hint : Integrable h) (hnn : ∀ x, 0 ≤ h x)
    (c L : ℝ) (hc : 0 < c) (hL : 0 ≤ L) :
    ∫ u in (0:ℝ)..L, c * h (c * u - 1) ≤ ∫ v, h v := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_sub _ hc.ne',
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
    intervalIntegral.integral_of_le (by nlinarith)]
  exact setIntegral_le_integral hint (ae_of_all _ hnn)

private noncomputable def chi (N u : ℝ) : ℝ := sTr (N * u - 1) * (1 - sTr (u / N - 1))
private noncomputable def chi1 (N u : ℝ) : ℝ :=
  N * d1 (N * u - 1) * (1 - sTr (u / N - 1)) - sTr (N * u - 1) * (d1 (u / N - 1) / N)
private noncomputable def chi2 (N u : ℝ) : ℝ :=
  N * N * d2 (N * u - 1) * (1 - sTr (u / N - 1)) - 2 * d1 (N * u - 1) * d1 (u / N - 1)
    - sTr (N * u - 1) * (d2 (u / N - 1) / (N * N))

private lemma in1 (N u : ℝ) : HasDerivAt (fun u : ℝ => N * u - 1) N u := by
  simpa using ((hasDerivAt_id u).const_mul N).sub_const 1

private lemma in2 (N u : ℝ) : HasDerivAt (fun u : ℝ => u / N - 1) (1 / N) u := by
  simpa using ((hasDerivAt_id u).div_const N).sub_const 1

private lemma chi_hasDeriv (N u : ℝ) (hN : N ≠ 0) : HasDerivAt (chi N) (chi1 N u) u := by
  have h1 := (st_hasDeriv (N * u - 1)).comp u (in1 N u)
  have h2 := (st_hasDeriv (u / N - 1)).comp u (in2 N u)
  have := h1.mul (h2.const_sub 1)
  refine this.congr_deriv ?_
  simp only [chi1, Function.comp]; field_simp; ring

private lemma chi1_hasDeriv (N u : ℝ) (hN : N ≠ 0) : HasDerivAt (chi1 N) (chi2 N u) u := by
  have h1 := (st_hasDeriv (N * u - 1)).comp u (in1 N u)
  have h2 := (st_hasDeriv (u / N - 1)).comp u (in2 N u)
  have g1 := (d1_hasDeriv (N * u - 1)).comp u (in1 N u)
  have g2 := (d1_hasDeriv (u / N - 1)).comp u (in2 N u)
  have := ((g1.const_mul N).mul (h2.const_sub 1)).sub (h1.mul (g2.div_const N))
  refine this.congr_deriv ?_
  simp only [chi2, Function.comp]; field_simp; ring

private lemma chi1_cont (N : ℝ) : Continuous (chi1 N) := by
  have := d1_cont; have := Real.smoothTransition.continuous
  unfold chi1; fun_prop

private lemma chi2_cont (N : ℝ) : Continuous (chi2 N) := by
  have := d1_cont; have := d2_cont; have := Real.smoothTransition.continuous
  unfold chi2; fun_prop

private lemma chi_zero (N : ℝ) : chi N 0 = 0 := by
  simp [chi, Real.smoothTransition.zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]

private lemma chi_eq_zero_of_ge (N u : ℝ) (hN : 1 ≤ N) (hu : 2 * N ≤ u) : chi N u = 0 := by
  have : 1 ≤ u / N - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]; linarith
  simp [chi, Real.smoothTransition.one_of_one_le this]

private lemma chi1_zero (N : ℝ) : chi1 N 0 = 0 := by
  have h : (-1 : ℝ) ∉ Icc (0 : ℝ) 1 := fun h => by linarith [h.1]
  simp [chi1, Real.smoothTransition.zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num), d1_zero h]

private lemma chi1_L (N : ℝ) (hN : 1 ≤ N) : chi1 N (2 * N + 1) = 0 := by
  have h1 : N * (2 * N + 1) - 1 ∉ Icc (0 : ℝ) 1 := fun h => by nlinarith [h.2]
  have h2 : (2 * N + 1) / N - 1 ∉ Icc (0 : ℝ) 1 := fun h => by
    have := h.2
    rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)] at this; linarith
  simp [chi1, d1_zero h1, d1_zero h2,
    Real.smoothTransition.one_of_one_le (show 1 ≤ (2 * N + 1) / N - 1 by
      rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]; linarith)]

private lemma chi_mem (N u : ℝ) : 0 ≤ chi N u ∧ chi N u ≤ 1 := by
  have a0 := Real.smoothTransition.nonneg (N * u - 1)
  have a1 := Real.smoothTransition.le_one (N * u - 1)
  have b0 := Real.smoothTransition.nonneg (u / N - 1)
  have b1 := Real.smoothTransition.le_one (u / N - 1)
  unfold chi
  exact ⟨mul_nonneg a0 (by linarith), by nlinarith⟩

private lemma E_hasDeriv (c : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (c * u)) (c * Complex.exp (c * u)) u := by
  have := (((hasDerivAt_id u).ofReal_comp).const_mul c).cexp
  simpa [mul_comm] using this

private lemma exp_diff (z1 z2 : ℂ) (h1 : z1.re ≤ 0) (h2 : z2.re ≤ 0) (u : ℝ) (hu : 0 ≤ u) :
    ‖Complex.exp (z1 * u) - Complex.exp (z2 * u)‖ ≤ u * ‖z1 - z2‖ := by
  have hs : Convex ℝ {z : ℂ | z.re ≤ 0} := convex_halfSpace_re_le 0
  have hd : ∀ z ∈ {z : ℂ | z.re ≤ 0},
      HasDerivWithinAt (fun z : ℂ => Complex.exp (z * u)) ((u : ℂ) * Complex.exp (z * u))
        {z : ℂ | z.re ≤ 0} z := by
    intro z _
    have := ((hasDerivAt_id z).mul_const (u : ℂ)).cexp
    exact (this.congr_deriv (by simp [mul_comm])).hasDerivWithinAt
  have hb : ∀ z ∈ {z : ℂ | z.re ≤ 0}, ‖(u : ℂ) * Complex.exp (z * u)‖ ≤ u := by
    intro z hz
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    have : (z * (u : ℂ)).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hz hu
    calc u * Real.exp (z * (u : ℂ)).re ≤ u * 1 := by
          gcongr; exact Real.exp_le_one_iff.2 this
      _ = u := mul_one u
  exact hs.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb h2 h1

private lemma G_bound (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hra : a.re ≤ 0) (hrb : b.re ≤ 0)
    (u : ℝ) (hu : 0 ≤ u) :
    ‖(Complex.exp (a * u) - 1) / a ^ 2 - (Complex.exp (b * u) - 1) / b ^ 2‖ ≤
      u * ‖a - b‖ * (3 / ‖a‖ ^ 2 + 1 / ‖b‖ ^ 2) := by
  have e : (Complex.exp (a * u) - 1) / a ^ 2 - (Complex.exp (b * u) - 1) / b ^ 2 =
      (Complex.exp (a * u) - Complex.exp (b * u)) / a ^ 2 +
        (Complex.exp (b * u) - Complex.exp (0 * u)) * ((b - a) * (b + a) / (a ^ 2 * b ^ 2)) := by
    rw [zero_mul, Complex.exp_zero]; field_simp; ring
  have k1 := exp_diff a b hra hrb u hu
  have k2 := exp_diff b 0 hrb le_rfl u hu
  rw [sub_zero] at k2
  have hx : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hy : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hab : ‖b - a‖ = ‖a - b‖ := norm_sub_rev _ _
  have hba : ‖b + a‖ ≤ ‖a‖ + ‖b‖ := by rw [add_comm]; exact norm_add_le _ _
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_mul, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hab]
  set x := ‖a‖; set y := ‖b‖; set q := ‖a - b‖
  have hq : 0 ≤ q := norm_nonneg _
  have t1 : ‖Complex.exp (a * u) - Complex.exp (b * u)‖ / x ^ 2 ≤ u * q / x ^ 2 := by gcongr
  have t2 : ‖Complex.exp (b * u) - Complex.exp (0 * u)‖ * (q * ‖b + a‖ / (x ^ 2 * y ^ 2)) ≤
      (u * y) * (q * (x + y) / (x ^ 2 * y ^ 2)) := by gcongr
  refine (add_le_add t1 t2).trans (le_of_eq_of_le (b := u * q * (2 / x ^ 2 + 1 / (x * y))) ?_ ?_)
  · field_simp; ring
  · have : 1 / (x * y) ≤ 1 / x ^ 2 + 1 / y ^ 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [sq_nonneg (x - y), mul_pos hx hy]
    have : 0 ≤ u * q := mul_nonneg hu hq
    refine mul_le_mul_of_nonneg_left ?_ this
    have e3 : 3 / x ^ 2 = 2 / x ^ 2 + 1 / x ^ 2 := by ring
    linarith

private lemma cpow_exp (u : ℝ) (z : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ z = Complex.exp (z * u) := by
  have h0 : ((Real.exp u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos u).ne'
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp,
    mul_comm]

private lemma mellin_u (n : ℕ) (s w : ℂ) :
    mellin (MasulloRH.regularizedTraceTest n s) w =
      ∫ u in (0:ℝ)..(2 * ((n:ℝ) + 1) + 1), ((chi ((n:ℝ) + 1) u : ℝ) : ℂ) *
        (Complex.exp ((w - s + 1 / 2) * u) - Complex.exp ((w - 2) * u)) := by
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hN : 1 ≤ N := by simp [hNdef]
  have step1 : mellin (MasulloRH.regularizedTraceTest n s) w =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) • MasulloRH.regularizedTraceTest n s t := by
    rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one)]
    intro t ht
    have : ¬ (1 < t) := ht.2
    simp [MasulloRH.regularizedTraceTest, this]
  have himg : Real.exp '' Ioi 0 = Ioi 1 := by
    ext t; constructor
    · rintro ⟨u, hu, rfl⟩; exact Real.one_lt_exp_iff.2 hu
    · intro ht
      exact ⟨Real.log t, Real.log_pos ht, Real.exp_log (lt_trans zero_lt_one ht)⟩
  rw [step1, ← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  have step2 : ∀ u ∈ Ioi (0:ℝ), |Real.exp u| • (((Real.exp u : ℝ) : ℂ) ^ (w - 1) •
      MasulloRH.regularizedTraceTest n s (Real.exp u)) =
      ((chi N u : ℝ) : ℂ) *
        (Complex.exp ((w - s + 1 / 2) * u) - Complex.exp ((w - 2) * u)) := by
    intro u hu
    have h1 : 1 < Real.exp u := Real.one_lt_exp_iff.2 hu
    simp only [MasulloRH.regularizedTraceTest, MasulloRH.traceLogCutoff, if_pos h1,
      Real.log_exp, abs_of_pos (Real.exp_pos u), smul_eq_mul, Complex.real_smul, chi]
    rw [← hNdef, cpow_exp, cpow_exp, cpow_exp, Complex.ofReal_exp]
    have ea : Complex.exp ((w - s + 1 / 2) * u) =
        Complex.exp u * (Complex.exp ((w - 1) * u) * Complex.exp ((1 / 2 - s) * u)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have eb : Complex.exp ((w - 2) * u) =
        Complex.exp u * (Complex.exp ((w - 1) * u) * Complex.exp ((-2 : ℂ) * u)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    rw [ea, eb]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi step2,
    intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  intro u hu
  have : 2 * N + 1 < u := by
    by_contra h; exact hu.2 ⟨hu.1, not_lt.1 h⟩
  rw [chi_eq_zero_of_ge N u hN (by linarith)]
  simp

private lemma ibp (N : ℝ) (hN : 1 ≤ N) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∫ u in (0:ℝ)..(2 * N + 1), ((chi N u : ℝ) : ℂ) *
        (Complex.exp (a * u) - Complex.exp (b * u)) =
      ∫ u in (0:ℝ)..(2 * N + 1), ((chi2 N u : ℝ) : ℂ) *
        ((Complex.exp (a * u) - 1) / a ^ 2 - (Complex.exp (b * u) - 1) / b ^ 2) := by
  have hN0 : N ≠ 0 := by positivity
  have hP : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (a * u) / a - Complex.exp (b * u) / b)
      (Complex.exp (a * u) - Complex.exp (b * u)) u := by
    intro u
    refine (((E_hasDeriv a u).div_const a).sub ((E_hasDeriv b u).div_const b)).congr_deriv ?_
    field_simp
  have hG : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => (Complex.exp (a * u) - 1) / a ^ 2 - (Complex.exp (b * u) - 1) / b ^ 2)
      (Complex.exp (a * u) / a - Complex.exp (b * u) / b) u := by
    intro u
    refine ((((E_hasDeriv a u).sub_const 1).div_const (a ^ 2)).sub
      (((E_hasDeriv b u).sub_const 1).div_const (b ^ 2))).congr_deriv ?_
    field_simp
  have c1 : Continuous (fun u : ℝ => ((chi1 N u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (chi1_cont N)
  have c2 : Continuous (fun u : ℝ => ((chi2 N u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (chi2_cont N)
  have i1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * N + 1)
    (fun u _ => (chi_hasDeriv N u hN0).ofReal_comp) (fun u _ => hP u)
    (c1.intervalIntegrable _ _) (by apply Continuous.intervalIntegrable; fun_prop)
  have i2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * N + 1)
    (fun u _ => (chi1_hasDeriv N u hN0).ofReal_comp) (fun u _ => hG u)
    (c2.intervalIntegrable _ _) (by apply Continuous.intervalIntegrable; fun_prop)
  rw [i1, i2, chi_zero, chi1_zero, chi1_L N hN,
    chi_eq_zero_of_ge N (2 * N + 1) hN (by linarith)]
  simp

private lemma chi2_pt (K1 : ℝ) (hK1 : ∀ x, |d1 x| ≤ K1) (N u : ℝ) (hN : 1 ≤ N) (hu : 0 ≤ u) :
    |chi2 N u| * u ≤ N * hw d2 (N * u - 1) + 2 * K1 * (N * hw d1 (N * u - 1)) +
      N⁻¹ * hw d2 (N⁻¹ * u - 1) := by
  have hN0 : 0 < N := by linarith
  have S1 := Real.smoothTransition.nonneg (N * u - 1)
  have S1' := Real.smoothTransition.le_one (N * u - 1)
  have S2 := Real.smoothTransition.nonneg (u / N - 1)
  have S2' := Real.smoothTransition.le_one (u / N - 1)
  have hr1 := hK1 (u / N - 1)
  have hK0 : 0 ≤ K1 := (abs_nonneg _).trans (hK1 0)
  have hdiv : N⁻¹ * u - 1 = u / N - 1 := by rw [div_eq_inv_mul]
  simp only [hw]
  rw [hdiv]
  set p := d2 (N * u - 1); set q := d1 (N * u - 1); set r := d1 (u / N - 1)
  set r2 := d2 (u / N - 1)
  set A := |N * u - 1| + 1
  set B := |u / N - 1| + 1
  have hA : N * u ≤ A := by have := le_abs_self (N * u - 1); simp only [A]; linarith
  have hB : u / N ≤ B := by have := le_abs_self (u / N - 1); simp only [B]; linarith
  have hu1 : u ≤ N * u := le_mul_of_one_le_left hu hN
  have hAp : 0 ≤ A := by positivity
  -- triangle inequality
  have tri : |chi2 N u| ≤ N * N * |p| + 2 * |q| * |r| + |r2| / (N * N) := by
    unfold chi2
    have e1 : |N * N * p * (1 - sTr (u / N - 1))| ≤ N * N * |p| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - sTr (u / N - 1)), abs_mul,
        abs_of_pos (by positivity : 0 < N * N)]
      exact mul_le_of_le_one_right (by positivity) (by linarith)
    have e2 : |2 * q * r| = 2 * |q| * |r| := by rw [abs_mul, abs_mul]; norm_num
    have e3 : |sTr (N * u - 1) * (r2 / (N * N))| ≤ |r2| / (N * N) := by
      rw [abs_mul, abs_of_nonneg S1, abs_div, abs_of_pos (by positivity : 0 < N * N)]
      exact mul_le_of_le_one_left (by positivity) S1'
    calc _ ≤ |N * N * p * (1 - sTr (u / N - 1)) - 2 * q * r| +
          |sTr (N * u - 1) * (r2 / (N * N))| := abs_sub _ _
      _ ≤ |N * N * p * (1 - sTr (u / N - 1))| + |2 * q * r| +
          |sTr (N * u - 1) * (r2 / (N * N))| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by rw [e2]; gcongr
  have t1 : N * N * |p| * u ≤ N * (|p| * A) := by
    have : N * N * |p| * u = N * |p| * (N * u) := by ring
    rw [this]; have := abs_nonneg p
    calc N * |p| * (N * u) ≤ N * |p| * A := by gcongr
      _ = _ := by ring
  have t2 : 2 * |q| * |r| * u ≤ 2 * K1 * (N * (|q| * A)) := by
    have hq := abs_nonneg q
    have hr := abs_nonneg r
    have : u ≤ N * A := by nlinarith
    calc 2 * |q| * |r| * u ≤ 2 * |q| * K1 * (N * A) := by gcongr
      _ = _ := by ring
  have t3 : |r2| / (N * N) * u ≤ N⁻¹ * (|r2| * B) := by
    have := abs_nonneg r2
    have e : |r2| / (N * N) * u = N⁻¹ * (|r2| * (u / N)) := by field_simp
    rw [e]; gcongr
  calc |chi2 N u| * u ≤ (N * N * |p| + 2 * |q| * |r| + |r2| / (N * N)) * u := by gcongr
    _ = N * N * |p| * u + 2 * |q| * |r| * u + |r2| / (N * N) * u := by ring
    _ ≤ _ := by gcongr

private lemma chi2_int (K1 : ℝ) (hK1 : ∀ x, |d1 x| ≤ K1) (N : ℝ) (hN : 1 ≤ N) :
    ∫ u in (0:ℝ)..(2 * N + 1), |chi2 N u| * u ≤
      2 * (∫ v, hw d2 v) + 2 * K1 * (∫ v, hw d1 v) := by
  have hN0 : 0 < N := by linarith
  have hL : (0:ℝ) ≤ 2 * N + 1 := by linarith
  have c1 : Continuous (hw d1) := by unfold hw; have := d1_cont; fun_prop
  have c2 : Continuous (hw d2) := by unfold hw; have := d2_cont; fun_prop
  have hc := chi2_cont N
  have I1 : IntervalIntegrable (fun u => N * hw d2 (N * u - 1)) volume 0 (2 * N + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  have I2 : IntervalIntegrable (fun u => 2 * K1 * (N * hw d1 (N * u - 1))) volume 0
      (2 * N + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  have I3 : IntervalIntegrable (fun u => N⁻¹ * hw d2 (N⁻¹ * u - 1)) volume 0 (2 * N + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  calc ∫ u in (0:ℝ)..(2 * N + 1), |chi2 N u| * u
      ≤ ∫ u in (0:ℝ)..(2 * N + 1), (N * hw d2 (N * u - 1) + 2 * K1 * (N * hw d1 (N * u - 1)) +
          N⁻¹ * hw d2 (N⁻¹ * u - 1)) := by
        apply intervalIntegral.integral_mono_on hL
        · apply Continuous.intervalIntegrable; fun_prop
        · exact (I1.add I2).add I3
        · intro u hu; exact chi2_pt K1 hK1 N u hN hu.1
    _ = (∫ u in (0:ℝ)..(2 * N + 1), N * hw d2 (N * u - 1)) +
          2 * K1 * (∫ u in (0:ℝ)..(2 * N + 1), N * hw d1 (N * u - 1)) +
          ∫ u in (0:ℝ)..(2 * N + 1), N⁻¹ * hw d2 (N⁻¹ * u - 1) := by
        rw [intervalIntegral.integral_add (I1.add I2) I3, intervalIntegral.integral_add I1 I2,
          intervalIntegral.integral_const_mul (2 * K1) (fun u => N * hw d1 (N * u - 1))]
    _ ≤ (∫ v, hw d2 v) + 2 * K1 * (∫ v, hw d1 v) + ∫ v, hw d2 v := by
        have hK0 : 0 ≤ K1 := (abs_nonneg _).trans (hK1 0)
        gcongr
        · exact comp_bound _ (hw_int d2 d2_cont d2_cs) (hw_nonneg d2) N _ hN0 hL
        · exact comp_bound _ (hw_int d1 d1_cont d1_cs) (hw_nonneg d1) N _ hN0 hL
        · exact comp_bound _ (hw_int d2 d2_cont d2_cs) (hw_nonneg d2) N⁻¹ _ (inv_pos.2 hN0) hL
    _ = _ := by ring

private lemma mellin_bound (K1 : ℝ) (hK1 : ∀ x, |d1 x| ≤ K1) (n : ℕ) (s w : ℂ)
    (ha : (w - s + 1 / 2).re < 0) (hb : (w - 2).re < 0) :
    ‖mellin (MasulloRH.regularizedTraceTest n s) w‖ ≤
      ‖(w - s + 1 / 2) - (w - 2)‖ * (3 / ‖w - s + 1 / 2‖ ^ 2 + 1 / ‖w - 2‖ ^ 2) *
        (2 * (∫ v, hw d2 v) + 2 * K1 * (∫ v, hw d1 v)) := by
  set a := w - s + 1 / 2
  set b := w - 2
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hN : 1 ≤ N := by simp [hNdef]
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  set D := ‖a - b‖ * (3 / ‖a‖ ^ 2 + 1 / ‖b‖ ^ 2)
  have hD : 0 ≤ D := by positivity
  have hL : (0:ℝ) ≤ 2 * N + 1 := by linarith
  rw [mellin_u, ibp N hN a b ha0 hb0]
  refine (intervalIntegral.norm_integral_le_integral_norm hL).trans ?_
  calc _ ≤ ∫ u in (0:ℝ)..(2 * N + 1), D * (|chi2 N u| * u) := by
        apply intervalIntegral.integral_mono_on hL
        · apply Continuous.intervalIntegrable
          have := chi2_cont N
          fun_prop
        · apply Continuous.intervalIntegrable
          have := chi2_cont N
          fun_prop
        · intro u hu
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have := G_bound a b ha0 hb0 ha.le hb.le u hu.1
          calc |chi2 N u| * _ ≤ |chi2 N u| * (u * D) := by
                gcongr
                simpa [D, mul_assoc] using this
            _ = _ := by ring
    _ = D * ∫ u in (0:ℝ)..(2 * N + 1), |chi2 N u| * u := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by gcongr; exact chi2_int K1 hK1 N hN

theorem solution (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2) (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ρ : MasulloRH.ZetaZerosInTraceStrip α),
      ‖MasulloRH.zetaTraceTerm (MasulloRH.regularizedTraceTest n s) α ρ‖ ≤
        C * MasulloRH.zeroDecayWeight α ρ := by
  obtain ⟨K1, hK1⟩ := d1_cont.bounded_above_of_compact_support d1_cs
  have hK1' : ∀ x, |d1 x| ≤ K1 := fun x => by simpa using hK1 x
  have hK0 : 0 ≤ K1 := (abs_nonneg _).trans (hK1' 0)
  set K := 2 * (∫ v, hw d2 v) + 2 * K1 * (∫ v, hw d1 v)
  have hK : 0 ≤ K := by
    have := integral_nonneg (μ := volume) (f := hw d2) (hw_nonneg d2)
    have := integral_nonneg (μ := volume) (f := hw d1) (hw_nonneg d1)
    positivity
  set σ := s.im
  set C := (K + 1) * (‖(5 / 2 : ℂ) - s‖ + 1) * (24 * (1 + σ ^ 2) + 1)
  refine ⟨C, by positivity, fun n ρ => ?_⟩
  obtain ⟨ρv, -, -, -, hρ⟩ := ρ
  set w : ℂ := ρv - 1 / 2
  set γ := ρv.im
  have hwre : w.re = ρv.re - 1 / 2 := by simp [w]
  have hwim : w.im = γ := by simp [w, γ]
  have hw1 := (abs_lt.1 hρ).1
  have hw2 := (abs_lt.1 hρ).2
  have ha : (w - s + 1 / 2).re < -1 / 2 := by simp [hwre]; linarith
  have hb : (w - 2).re < -3 / 2 := by simp [hwre]; linarith
  have hmb := mellin_bound K1 hK1' n s w (by linarith) (by linarith)
  have hab : (w - s + 1 / 2) - (w - 2) = (5 / 2 : ℂ) - s := by ring
  rw [hab] at hmb
  -- lower bounds on the norms
  have hγ : 0 < 1 + γ ^ 2 := by positivity
  have na : (1 + γ ^ 2) ≤ 8 * (1 + σ ^ 2) * ‖w - s + 1 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre := ha
    have him : (w - s + 1 / 2).im = γ - σ := by simp [hwim, σ]
    rw [him]
    set r := (w - s + 1 / 2).re
    have hr : 1 / 4 ≤ r * r := by nlinarith
    nlinarith [sq_nonneg (γ - σ), sq_nonneg (γ - 2 * σ), mul_nonneg (sq_nonneg σ) (sq_nonneg (γ - σ))]
  have nb : (1 + γ ^ 2) ≤ ‖w - 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have him : (w - 2).im = γ := by simp [hwim]
    rw [him]
    nlinarith
  have hapos : 0 < ‖w - s + 1 / 2‖ ^ 2 := by
    have : (0:ℝ) < 8 * (1 + σ ^ 2) := by positivity
    by_contra h; push Not at h; nlinarith
  have hbpos : 0 < ‖w - 2‖ ^ 2 := by linarith
  have q1 : 3 / ‖w - s + 1 / 2‖ ^ 2 ≤ 24 * (1 + σ ^ 2) / (1 + γ ^ 2) := by
    rw [div_le_div_iff₀ hapos hγ]; nlinarith
  have q2 : 1 / ‖w - 2‖ ^ 2 ≤ 1 / (1 + γ ^ 2) := by
    rw [div_le_div_iff₀ hbpos hγ]; nlinarith
  have hmel : ‖mellin (MasulloRH.regularizedTraceTest n s) w‖ ≤ C / (1 + γ ^ 2) := by
    refine hmb.trans ?_
    have e : C / (1 + γ ^ 2) =
        ((‖(5 / 2 : ℂ) - s‖ + 1) * ((24 * (1 + σ ^ 2) + 1) / (1 + γ ^ 2))) * (K + 1) := by
      simp only [C]; ring
    rw [e]
    have : 3 / ‖w - s + 1 / 2‖ ^ 2 + 1 / ‖w - 2‖ ^ 2 ≤ (24 * (1 + σ ^ 2) + 1) / (1 + γ ^ 2) := by
      rw [add_div]; linarith
    have h0 : 0 ≤ 3 / ‖w - s + 1 / 2‖ ^ 2 + 1 / ‖w - 2‖ ^ 2 := by positivity
    have h1 : ‖(5 / 2 : ℂ) - s‖ * (3 / ‖w - s + 1 / 2‖ ^ 2 + 1 / ‖w - 2‖ ^ 2) ≤
        (‖(5 / 2 : ℂ) - s‖ + 1) * ((24 * (1 + σ ^ 2) + 1) / (1 + γ ^ 2)) :=
      mul_le_mul (by linarith) this h0 (by positivity)
    exact mul_le_mul h1 (by linarith) hK (by positivity)
  simp only [MasulloRH.zetaTraceTerm, MasulloRH.zeroDecayWeight]
  rw [norm_mul, Complex.norm_natCast]
  set m := (analyticOrderNatAt riemannZeta ρv : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  calc m * ‖mellin (MasulloRH.regularizedTraceTest n s) w‖ ≤ m * (C / (1 + γ ^ 2)) := by gcongr
    _ = C * (m / (1 + γ ^ 2)) := by ring

