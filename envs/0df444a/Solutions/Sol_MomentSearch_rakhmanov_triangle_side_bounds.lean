-- Prove2me | solution 1 for MomentSearch.rakhmanov_triangle_side_bounds
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:11:46.164145+00:00
-- url     : https://prove2.me/submissions/b6b4e448-a4c2-42a7-87bd-864224b3839b

import Theorems.Thm_MomentSearch_rakhmanov_triangle_phase_geometry
import Mathlib

open scoped Real

/-- The real and imaginary parts of the contour logarithm give the same
triangle-side constants when estimated together. -/
theorem triangleLogBounds (b : ℂ) (hsector : Real.sqrt 3 * |b.im| ≤ b.re) :
    let logTerm := Complex.log (1 + Complex.exp (-b))
    |logTerm.im| ≤ b.re * Real.exp (-b.re) / Real.sqrt 3 ∧
    -(Real.sqrt 3 * Real.log 2) - 1 / (Real.exp 1 * Real.sqrt 3) ≤
      logTerm.im - Real.sqrt 3 * logTerm.re ∧
    logTerm.im - Real.sqrt 3 * logTerm.re ≤ 1 / (Real.exp 1 * Real.sqrt 3) := by
  let s : ℝ := Real.sqrt 3
  let p : ℝ := Real.exp (-b.re)
  let z : ℂ := 1 + Complex.exp (-b)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hslo : (17 / 10 : ℝ) ≤ s := by nlinarith only [hs2, hs0]
  have hshi : s ≤ 7 / 4 := by nlinarith only [hs2, hs0]
  have hR0 : 0 ≤ b.re := (mul_nonneg hs0.le (abs_nonneg _)).trans hsector
  have hp0 : 0 < p := Real.exp_pos _
  have hp1 : p ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hz_re : z.re = 1 + p * Real.cos b.im := by
    simp [z, p, Complex.exp_re]
  have hz_im : z.im = -(p * Real.sin b.im) := by
    simp [z, p, Complex.exp_im]
  have hsector_large (h : Real.pi / 2 ≤ |b.im|) : (8 / 3 : ℝ) ≤ b.re := by
    calc
      _ ≤ (17 / 10 : ℝ) * (3.14 / 2) := by norm_num
      _ ≤ s * |b.im| := mul_le_mul hslo (by linarith [Real.pi_gt_d2, h]) (by norm_num) hs0.le
      _ ≤ _ := hsector
  have hp_small (h : Real.pi / 2 ≤ |b.im|) : p ≤ 1 / 14 := by
    have h14 : (14 : ℝ) < Real.exp (8/3) := by
      calc
        _ < ∑ j ∈ Finset.range 8, (8 / 3 : ℝ) ^ j / (j.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ]
        _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 8
    have h := h14.le.trans (Real.exp_le_exp.mpr (hsector_large h))
    simpa [p, Real.exp_neg, one_div] using (one_div_le_one_div_of_le (by norm_num) h)
  have hcos (h : |b.im| ≤ Real.pi / 2) : 0 ≤ Real.cos b.im :=
    Real.cos_nonneg_of_mem_Icc (abs_le.mp h)
  have hre : 0 < z.re := by
    rw [hz_re]
    by_cases h : |b.im| ≤ Real.pi / 2
    · linarith [mul_nonneg hp0.le (hcos h)]
    · have hp := hp_small (le_of_lt (lt_of_not_ge h))
      have hm := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos b.im) hp0.le
      linarith
  have hnormpos : 0 < ‖z‖ := hre.trans_le (Complex.re_le_norm _)
  have hnormupper : ‖z‖ ≤ 2 := by
    have := norm_add_le (1 : ℂ) (Complex.exp (-b))
    simp only [norm_one, Complex.norm_exp, Complex.neg_re] at this
    linarith only [show ‖z‖ ≤ 1 + p from this, hp1]
  have hlogupper : (Complex.log z).re ≤ Real.log 2 := by
    rw [Complex.log_re]
    exact Real.log_le_log hnormpos hnormupper
  have harg : |(Complex.log z).im| ≤ |z.im| / z.re := by
    rw [Complex.log_im]
    have hphase := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
    have he : Real.arctan (z.im / z.re) = z.arg := by
      rw [← Complex.tan_arg]
      exact Real.arctan_tan hphase.1 hphase.2
    have hdiv : |z.im / z.re| = |z.im| / z.re := by rw [abs_div, abs_of_pos hre]
    rw [← he, ← hdiv]
    generalize z.im / z.re = u
    have harc (v : ℝ) (hv : 0 ≤ v) : Real.arctan v ≤ v := by
      have h := Real.le_tan (Real.arctan_nonneg.mpr hv) (Real.arctan_lt_pi_div_two v)
      rwa [Real.tan_arctan] at h
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu, abs_of_nonneg (Real.arctan_nonneg.mpr hu)]
      exact harc _ hu
    · have hu' : 0 ≤ -u := by linarith
      rw [abs_of_nonpos (by linarith : u ≤ 0),
        abs_of_nonpos (Real.arctan_le_zero.mpr (by linarith : u ≤ 0)), ← Real.arctan_neg]
      exact harc _ hu'
  let T : ℝ := 1 / (Real.exp 1 * s)
  have hlarge_arg (h : Real.pi / 2 ≤ |b.im|) : |(Complex.log z).im| ≤ p / (1-p) := by
    have hre' : 1 - p ≤ z.re := by
      rw [hz_re]
      linarith [mul_le_mul_of_nonneg_left (Real.neg_one_le_cos b.im) hp0.le]
    have h1p : 0 < 1 - p := by linarith [hp_small h]
    have him' : |z.im| ≤ p := by
      rw [hz_im, abs_neg, abs_mul, abs_of_pos hp0]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one b.im) hp0.le
    exact harg.trans (div_le_div_of_nonneg_left (abs_nonneg _) h1p hre' |>.trans
      (div_le_div_of_nonneg_right him' h1p.le))
  have him : |(Complex.log z).im| ≤ b.re * p / s := by
    by_cases h : |b.im| ≤ Real.pi / 2
    · have hre1 : 1 ≤ z.re := by rw [hz_re]; linarith [mul_nonneg hp0.le (hcos h)]
      have ha := (div_le_iff₀ hre).2 (show |z.im| ≤ |z.im| * z.re by
        simpa using mul_le_mul_of_nonneg_left hre1 (abs_nonneg z.im))
      refine harg.trans (ha.trans ?_)
      rw [hz_im, abs_neg, abs_mul, abs_of_pos hp0]
      apply (le_div_iff₀ hs0).2
      have hsine := mul_le_mul_of_nonneg_left (show |Real.sin b.im| ≤ |b.im| from Real.abs_sin_le_abs) hs0.le
      nlinarith only [mul_le_mul_of_nonneg_left (hsine.trans hsector) hp0.le]
    · have h' : Real.pi / 2 ≤ |b.im| := (lt_of_not_ge h).le
      have hp := hp_small h'
      have hbr : (14 / 13 : ℝ) ≤ b.re / s := by
        apply (le_div_iff₀ hs0).mpr
        linarith only [hsector_large h', hshi]
      refine (hlarge_arg h').trans ?_
      rw [mul_comm b.re, mul_div_assoc, div_eq_mul_inv p]
      refine mul_le_mul_of_nonneg_left (?_ : (1 - p)⁻¹ ≤ b.re / s) hp0.le
      apply le_trans _ hbr
      have h1p : 0 < 1 - p := by linarith
      rw [← one_div]
      apply (div_le_iff₀ h1p).2
      linarith only [hp]
  have himT : |(Complex.log z).im| ≤ T := by
    refine him.trans ?_
    exact (div_le_div_of_nonneg_right (Real.mul_exp_neg_le_exp_neg_one _) hs0.le).trans_eq
      (by rw [Real.exp_neg]; simp only [T, div_eq_mul_inv, one_mul, mul_inv_rev]; ring)
  change |(Complex.log z).im| ≤ b.re * p / s ∧
    -(s * Real.log 2) - T ≤ (Complex.log z).im - s * (Complex.log z).re ∧
    (Complex.log z).im - s * (Complex.log z).re ≤ T
  refine ⟨him, ?_, ?_⟩
  · linarith only [(abs_le.mp himT).1, mul_le_mul_of_nonneg_left hlogupper hs0.le]
  · by_cases h : |b.im| ≤ Real.pi / 2
    · have hre1 : 1 ≤ z.re := by rw [hz_re]; linarith [mul_nonneg hp0.le (hcos h)]
      have hL : 0 ≤ (Complex.log z).re := by
        rw [Complex.log_re]
        exact Real.log_nonneg (hre1.trans (Complex.re_le_norm _))
      linarith only [(abs_le.mp himT).2, mul_nonneg hs0.le hL]
    · have h' := (lt_of_not_ge h).le
      have hp := hp_small h'
      have h1p : 0 < 1 - p := by linarith
      have hre' : 1 - p ≤ z.re := by
        rw [hz_re]
        linarith [mul_le_mul_of_nonneg_left (Real.neg_one_le_cos b.im) hp0.le]
      have hLR : -(Complex.log z).re ≤ p / (1-p) := by
        rw [Complex.log_re]
        have hL := Real.log_le_log h1p (hre'.trans (Complex.re_le_norm _))
        have hInv := Real.log_le_sub_one_of_pos (inv_pos.mpr h1p)
        rw [Real.log_inv] at hInv
        have hrat : (1 - p)⁻¹ - 1 = p / (1 - p) := by field_simp; ring
        linarith only [hL, hInv, hrat]
      have h13 : p / (1-p) ≤ 1 / 13 := (div_le_iff₀ h1p).2 (by linarith only [hp])
      have hT : (1+s) / 13 ≤ T := by
        apply (le_div_iff₀ (mul_pos (Real.exp_pos _) hs0)).2
        have he : Real.exp 1 ≤ (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
        calc
          _ = Real.exp 1 * ((s^2 + s) / 13) := by ring
          _ ≤ (68 / 25 : ℝ) * ((3 + 7 / 4) / 13) := by
            rw [hs2]
            exact mul_le_mul he (by linarith only [hshi]) (by positivity) (by norm_num)
          _ ≤ 1 := by norm_num
      calc
        _ ≤ (1+s) * (p / (1-p)) := by
          linarith only [(le_abs_self _).trans (hlarge_arg h'), mul_le_mul_of_nonneg_left hLR hs0.le]
        _ ≤ (1+s) * (1 / 13) := mul_le_mul_of_nonneg_left h13 (by positivity)
        _ = (1+s) / 13 := by ring
        _ ≤ T := hT

private theorem triangle_den_pos (y t : ℝ) (hy : y ≠ 0) :
    0 < y^2-y*t+t^2 := by
  have h := sq_pos_of_ne_zero hy
  nlinarith only [h, sq_nonneg (t - y/2)]

private theorem triangle_kernel_integral (y : ℝ) (hy : y ≠ 0) :
    let I := ∫ t in (0 : ℝ)..2, y / (y^2-y*t+t^2)
    (0 < y → 0 ≤ I ∧ I ≤ 4 * Real.pi / (3 * Real.sqrt 3)) ∧
    (y < 0 → -(2 * Real.pi / (3 * Real.sqrt 3)) ≤ I ∧ I ≤ 0) := by
  let s : ℝ := Real.sqrt 3
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s^2 = 3 := Real.sq_sqrt (by norm_num)
  let F (t : ℝ) := (2 / s) * Real.arctan ((2*t-y)/(s*y))
  have hF : Continuous F := by unfold F; fun_prop
  have hderiv (t : ℝ) : HasDerivAt F (y / (y^2-y*t+t^2)) t := by
    let v : ℝ := (2*t-y)/(s*y)
    have hv : HasDerivAt (fun t : ℝ => (2*t-y)/(s*y)) (2/(s*y)) t := by
      simpa only [mul_one] using (((hasDerivAt_id' t).const_mul 2).sub_const y).div_const (s*y)
    have hd := ((Real.hasDerivAt_arctan v).comp t hv).const_mul (2 / s)
    have he : (2/s) * ((1/(1+v^2))*(2/(s*y))) = y/(y^2-y*t+t^2) := by
      have hden : 1 + v^2 = (4 * (y^2-y*t+t^2))/(s*y)^2 := by
        dsimp [v]
        rw [div_pow]
        apply (eq_div_iff (pow_ne_zero _ (mul_ne_zero hs.ne' hy))).2
        calc
          _ = (s*y)^2 + (2*t-y)^2 := by field_simp
          _ = _ := by linear_combination y^2 * hs2
      rw [hden, one_div_div]
      field_simp [hs.ne', hy, (triangle_den_pos y t hy).ne']
      norm_num
    rw [he] at hd
    exact hd
  have hcont : Continuous (fun t : ℝ => y / (y^2-y*t+t^2)) :=
    continuous_const.div (by fun_prop) (fun t => (triangle_den_pos y t hy).ne')
  have heq : (∫ t in (0 : ℝ)..2, y / (y^2-y*t+t^2)) =
      2/s * (Real.arctan ((4-y)/(s*y)) + Real.pi/6) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hF.continuousOn
      (fun t _ => hderiv t) (hcont.intervalIntegrable _ _)]
    dsimp [F]
    rw [show (2*(0:ℝ)-y)/(s*y) = -s⁻¹ by field_simp; ring,
      Real.arctan_neg, Real.arctan_inv_sqrt_three]
    ring
  dsimp
  constructor
  · intro hy'
    constructor
    · exact intervalIntegral.integral_nonneg (by norm_num)
        (fun t _ => div_nonneg hy'.le (triangle_den_pos y t hy).le)
    · rw [heq]
      have h := Real.arctan_lt_pi_div_two ((4-y)/(s*y))
      calc
        _ ≤ 2/s * (Real.pi/2 + Real.pi/6) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by ring
  · intro hy'
    constructor
    · rw [heq]
      have h := Real.neg_pi_div_two_lt_arctan ((4-y)/(s*y))
      calc
        _ = 2/s * (-(Real.pi/2) + Real.pi/6) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
          (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 2) (intervalIntegrable_const (c := (0 : ℝ)))
          (fun t _ => div_nonpos_of_nonpos_of_nonneg hy'.le (triangle_den_pos y t hy).le)
      simpa using hmono

private theorem triangle_log_continuous (B : ℝ → ℂ)
    (hB : ContinuousOn B (Set.Icc 0 2))
    (hsector : ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re) :
    ContinuousOn (fun t => Complex.log (1 + Complex.exp (-(B t)))) (Set.Icc 0 2) := by
  let s := Real.sqrt 3
  have hs : 0 < s := by dsimp [s]; positivity
  have heB : ContinuousOn (fun t => (1 : ℂ) + Complex.exp (-(B t))) (Set.Icc 0 2) :=
    continuousOn_const.add (Complex.continuous_exp.comp_continuousOn hB.neg)
  have hpositive (t : ℝ) (ht : t ∈ Set.Icc 0 2) :
      0 < (1 + Complex.exp (-(B t))).re := by
    have hr0 : 0 ≤ (B t).re := (mul_nonneg hs.le (abs_nonneg _)).trans (hsector t ht)
    by_cases hz : 0 < (B t).re
    · have hq : Real.exp (-(B t).re) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hc := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (B t).im)
        (Real.exp_pos (-(B t).re)).le
      simp only [Complex.add_re, Complex.one_re, Complex.exp_re, Complex.neg_re,
        Complex.neg_im, Real.cos_neg]
      linarith
    · have hr : (B t).re = 0 := le_antisymm (le_of_not_gt hz) hr0
      have hi : (B t).im = 0 := abs_eq_zero.mp (le_antisymm
        (nonpos_of_mul_nonpos_right (hr ▸ hsector t ht) hs) (abs_nonneg _))
      simp only [Complex.add_re, Complex.one_re, Complex.exp_re, Complex.neg_re,
        Complex.neg_im, hr, hi, neg_zero, Real.exp_zero, Real.cos_zero, mul_one]
      norm_num
  intro t ht
  have h : ContinuousAt Complex.log (1 + Complex.exp (-(B t))) :=
    continuousAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl (hpositive t ht)))
  exact h.comp_continuousWithinAt (f := fun t => 1 + Complex.exp (-(B t))) (heB t ht)


private theorem triangle_half_integral_bounds
    (B : ℝ → ℂ) (d : ℝ → ℝ)
    (hB : ContinuousOn B (Set.Icc 0 2)) (hd : ContinuousOn d (Set.Icc 0 2))
    (h0 : (B 0).re = 0)
    (hderiv : ∀ t ∈ Set.Ioo 0 2, HasDerivAt (fun t => (B t).re) (d t) t)
    (hslope : ∀ t ∈ Set.Ioo 0 2, (B t).re / t ≤ d t)
    (hsector : ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re)
    (y : ℝ) (hy : y ≠ 0) :
    let Λ : ℝ → ℂ := fun t => Complex.log (1 + Complex.exp (-(B t)))
    let K : ℝ → ℝ := fun t => y^2-y*t+t^2
    let η := (1 / (2 * Real.pi)) *
      (∫ t in (0 : ℝ)..2, ((Λ t).im - Real.sqrt 3 * (Λ t).re) * (y / K t)) -
      (1 / Real.pi) * ∫ t in (0 : ℝ)..2, (Λ t).im * (t / K t)
    let D := 2 / (9 * Real.exp 1) + 4 / (3 * Real.pi * Real.sqrt 3)
    (0 < y → -(2/3) * Real.log 2 - D ≤ η ∧ η ≤ D) ∧
      (y < 0 → -D ≤ η ∧ η ≤ (1/3) * Real.log 2 + D) := by
  intro Λ K η D
  let s := Real.sqrt 3
  let T := 1 / (Real.exp 1*s)
  let R (t : ℝ) := (B t).re
  let A (t : ℝ) := (Λ t).im - s * (Λ t).re
  let J (t : ℝ) := (Λ t).im
  let M := s * Real.log 2 + T
  have hs : 0 < s := by dsimp [s]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]; exact add_nonneg (mul_nonneg hs.le (Real.log_nonneg (by norm_num))) hT
  have hR : ContinuousOn R (Set.Icc 0 2) := Complex.continuous_re.comp_continuousOn hB
  have hΛ : ContinuousOn Λ (Set.Icc 0 2) := triangle_log_continuous B hB hsector
  have hJ : ContinuousOn J (Set.Icc 0 2) := Complex.continuous_im.comp_continuousOn hΛ
  have hA : ContinuousOn A (Set.Icc 0 2) :=
    hJ.sub (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hΛ))
  have hK (t : ℝ) : 0 < K t := triangle_den_pos _ _ hy
  have hkc : Continuous K := by unfold K; fun_prop
  have hcy : ContinuousOn (fun t => y / K t) (Set.uIcc 0 2) :=
    (continuous_const.div hkc (fun t => (hK t).ne')).continuousOn
  have hct : ContinuousOn (fun t => t / K t) (Set.uIcc 0 2) :=
    (continuous_id.div hkc (fun t => (hK t).ne')).continuousOn
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hcy hct
  have intA := (hA.mul hcy).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)
  have intJ := (hJ.mul hct).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)
  have hp (t : ℝ) (ht : t ∈ Set.Icc 0 2) :
      |J t| ≤ R t * Real.exp (-R t) / s ∧ -M ≤ A t ∧ A t ≤ T := by
    dsimp only [M, T, R, J, A, Λ, s]
    simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using triangleLogBounds (B t) (hsector t ht)
  let C := 4 / (3 * s)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdExp : ContinuousOn (fun t => Real.exp (-R t) * d t) (Set.Icc 0 2) :=
    hR.neg.rexp.mul hd
  have intD := hdExp.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)
  have h_intD : (∫ t in (0 : ℝ)..2, Real.exp (-R t) * d t) ≤ 1 := by
    have hc : ContinuousOn (fun t => -Real.exp (-R t)) (Set.Icc 0 2) := hR.neg.rexp.neg
    have hd' (t : ℝ) (ht : t ∈ Set.Ioo 0 2) :
        HasDerivAt (fun t => -Real.exp (-R t)) (Real.exp (-R t) * d t) t := by
      have hD : HasDerivAt (fun u => -R u) (-d t) t := (hderiv t ht).neg
      have he : HasDerivAt (fun u => Real.exp (-R u)) (Real.exp (-R t) * -d t) t :=
        hD.exp
      have hn : HasDerivAt (fun u => -Real.exp (-R u)) (-(Real.exp (-R t) * -d t)) t :=
        he.neg
      rwa [mul_neg, neg_neg] at hn
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hc hd' intD]
    have h0' : R 0 = 0 := h0
    rw [h0', neg_zero, Real.exp_zero]
    linarith [Real.exp_pos (-R 2)]
  have h_absJ :
      |∫ t in (0 : ℝ)..2, J t * (t / K t)| ≤ C := by
    have h_int := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 2)
      intJ.abs (intD.const_mul C) (fun t ht => ?_)
    · have hi : |∫ t in (0 : ℝ)..2, J t * (t / K t)| ≤
          ∫ t in (0 : ℝ)..2, |J t * (t / K t)| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm (f := fun t => J t * (t / K t))
            (by norm_num : (0 : ℝ) ≤ 2))
      rw [intervalIntegral.integral_const_mul] at h_int
      exact hi.trans (h_int.trans (by simpa using mul_le_mul_of_nonneg_left h_intD hC))
    · have ht' : t ∈ Set.Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2.le⟩
      have hratio : t / K t ≤ (4 / 3) / t := by
        apply (div_le_iff₀ (hK t)).2
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ ht.1).2
        change t*t ≤ 4/3 * (y^2-y*t+t^2)
        nlinarith only [sq_nonneg (y-t/2)]
      change |J t * (t / K t)| ≤ _
      rw [abs_mul, abs_of_nonneg (div_nonneg ht.1.le (hK t).le)]
      calc
        _ ≤ (R t * Real.exp (-R t) / s) * ((4 / 3) / t) :=
          mul_le_mul (hp t ht').1 hratio (div_nonneg ht.1.le (hK t).le)
            ((abs_nonneg _).trans (hp t ht').1)
        _ = C * (Real.exp (-R t) * (R t / t)) := by dsimp [C]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hslope t ht) (Real.exp_pos _).le) hC
  have hscaledJ :
      |(1 / Real.pi) * ∫ t in (0 : ℝ)..2, J t * (t / K t)| ≤
          4 / (3 * Real.pi * s) := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
    calc
      _ ≤ (1 / Real.pi) * C :=
        mul_le_mul_of_nonneg_left h_absJ (by positivity)
      _ = _ := by dsimp [C]; ring
  let I := ∫ t in (0 : ℝ)..2, y / K t
  let H := ∫ t in (0 : ℝ)..2, A t * (y / K t)
  let G := (1 / Real.pi) * ∫ t in (0 : ℝ)..2, J t * (t / K t)
  have hconst (c : ℝ) :
      IntervalIntegrable (fun t => c * (y / K t)) MeasureTheory.volume 0 2 :=
    (hcy.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)).const_mul c
  have hcomp {a b : ℝ} (hL : ∀ t ∈ Set.Icc (0 : ℝ) 2, a * (y / K t) ≤ A t * (y / K t))
      (hU : ∀ t ∈ Set.Icc (0 : ℝ) 2, A t * (y / K t) ≤ b * (y / K t)) :
      a * I ≤ H ∧ H ≤ b * I := by
    have hl := intervalIntegral.integral_mono_on (by norm_num) (hconst a) intA hL
    have hu := intervalIntegral.integral_mono_on (by norm_num) intA (hconst b) hU
    rw [intervalIntegral.integral_const_mul] at hl hu
    exact ⟨hl, hu⟩
  have hscale : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  change (0 < y → -(2/3) * Real.log 2 - D ≤ (1 / (2*Real.pi))*H - G ∧
      (1 / (2*Real.pi))*H - G ≤ D) ∧
    (y < 0 → -D ≤ (1 / (2*Real.pi))*H - G ∧
      (1 / (2*Real.pi))*H - G ≤ (1/3) * Real.log 2 + D)
  constructor
  · intro h
    have hI := (triangle_kernel_integral y hy).1 h
    change 0 ≤ I ∧ I ≤ 4 * Real.pi / (3 * s) at hI
    have hk (t : ℝ) : 0 ≤ y / K t := div_nonneg h.le (hK _).le
    obtain ⟨hl, hu⟩ := hcomp
      (fun t ht => mul_le_mul_of_nonneg_right (hp t ht).2.1 (hk t))
      (fun t ht => mul_le_mul_of_nonneg_right (hp t ht).2.2 (hk t))
    have hl := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonpos_left hI.2 (neg_nonpos.mpr hM)).trans hl) hscale
    have hu := mul_le_mul_of_nonneg_left
      (hu.trans (mul_le_mul_of_nonneg_left hI.2 hT)) hscale
    have heL : (1 / (2 * Real.pi)) * (-M * (4 * Real.pi / (3 * s))) =
        -(2/3) * Real.log 2 - 2 / (9 * Real.exp 1) := by
      dsimp [M, T]
      field_simp [hs.ne', Real.pi_ne_zero]
      have hs2 : s^2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [hs2]
      ring
    have heU : (1 / (2 * Real.pi)) * (T * (4 * Real.pi / (3 * s))) =
        2 / (9 * Real.exp 1) := by
      dsimp [T]
      field_simp [hs.ne', Real.pi_ne_zero]
      have hs2 : s^2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [hs2]
      norm_num
    rw [heL] at hl
    rw [heU] at hu
    change |G| ≤ 4 / (3 * Real.pi * Real.sqrt 3) at hscaledJ
    dsimp [D]
    exact ⟨by linarith only [hl, (abs_le.mp hscaledJ).2],
      by linarith only [hu, (abs_le.mp hscaledJ).1]⟩
  · intro h
    have hI := (triangle_kernel_integral y hy).2 h
    change -(2 * Real.pi / (3 * s)) ≤ I ∧ I ≤ 0 at hI
    have hk (t : ℝ) : y / K t ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h.le (hK _).le
    obtain ⟨hl, hu⟩ := hcomp
      (fun t ht => mul_le_mul_of_nonpos_right (hp t ht).2.2 (hk t))
      (fun t ht => mul_le_mul_of_nonpos_right (hp t ht).2.1 (hk t))
    have hl := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hI.1 hT).trans hl) hscale
    have hu := mul_le_mul_of_nonneg_left
      (hu.trans (mul_le_mul_of_nonpos_left hI.1 (neg_nonpos.mpr hM))) hscale
    have heL : (1 / (2 * Real.pi)) * (T * -(2 * Real.pi / (3 * s))) =
        - (1 / (9 * Real.exp 1)) := by
      dsimp [T]
      field_simp [hs.ne', Real.pi_ne_zero]
      have hs2 : s^2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [hs2]
      norm_num
    have heU : (1 / (2 * Real.pi)) * (-M * -(2 * Real.pi / (3 * s))) =
        (1/3) * Real.log 2 + 1 / (9 * Real.exp 1) := by
      dsimp [M, T]
      field_simp [hs.ne', Real.pi_ne_zero]
      have hs2 : s^2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [hs2]
      ring
    rw [heL] at hl
    rw [heU] at hu
    change |G| ≤ 4 / (3 * Real.pi * Real.sqrt 3) at hscaledJ
    have hExtra : 0 ≤ (1 : ℝ) / (9 * Real.exp 1) := by positivity
    dsimp [D]
    rw [show (2 : ℝ) / (9 * Real.exp 1) = 2 * (1 / (9 * Real.exp 1)) by ring]
    exact ⟨by linarith only [hl, (abs_le.mp hscaledJ).2, hExtra],
      by linarith only [hu, (abs_le.mp hscaledJ).1, hExtra]⟩

private theorem triangle_transform (r x : ℝ) (hr : 0 < r) (hx : x ≠ r)
    (Λ : ℝ → ℂ) (hΛ : ContinuousOn Λ (Set.Icc 0 2)) :
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z (t : ℝ) : ℂ := (r : ℂ) * (1 - s * t)
    let y := 1 - x / r
    let K (t : ℝ) := y^2-y*t+t^2
    ((∫ t in (0 : ℝ)..2, Λ t * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi) =
      (1/(2*Real.pi)) * (∫ t in (0 : ℝ)..2,
        ((Λ t).im - Real.sqrt 3 * (Λ t).re) * (y / K t)) -
        (1/Real.pi) * ∫ t in (0 : ℝ)..2, (Λ t).im * (t / K t) := by
  intro s Z y K
  have hxry : x = r * (1-y) := by dsimp [y]; field_simp; ring
  have hy : y ≠ 0 := by
    intro hy'
    apply hx
    rw [hxry, hy', sub_zero, mul_one]
  have hK (t : ℝ) : 0 < K t := triangle_den_pos _ _ hy
  have hss : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : s^2 - s + 1 = 0 := by
    apply Complex.ext
    · norm_num [s, pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re]
      nlinarith only [hss]
    · norm_num [s, pow_two, Complex.mul_im, Complex.sub_im, Complex.add_im]
      ring
  have hs_ne : s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [s] at he
  have hom (t : ℝ) :
      -(r : ℂ) * s * (K t : ℂ) = (s * (y : ℂ) - (t : ℂ)) * ((x : ℂ) - Z t) := by
    have hx' : (x : ℂ) = (r : ℂ) * (1 - (y : ℂ)) := by exact_mod_cast hxry
    rw [hx']
    simp only [K, Z, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
    linear_combination -(r : ℂ) * (y : ℂ) * (t : ℂ) * hs
  have hden (t : ℝ) : (x : ℂ) - Z t ≠ 0 := by
    intro h
    have he := hom t
    rw [h, mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hr.ne')) hs_ne)
      (Complex.ofReal_ne_zero.mpr (hK t).ne')) he
  have hF (t : ℝ) : Λ t * (-(r : ℂ) * s) / ((x : ℂ) - Z t) =
      Λ t * ((s * (y : ℂ) - (t : ℂ)) / (K t : ℂ)) := by
    rw [mul_div_assoc]
    congr 1
    exact (div_eq_div_iff (hden t) (Complex.ofReal_ne_zero.mpr (hK t).ne')).mpr (hom t)
  let F (t : ℝ) := Λ t * (-(r : ℂ) * s) / ((x : ℂ) - Z t)
  let P (t : ℝ) := ((Λ t).im - Real.sqrt 3 * (Λ t).re) * (y / K t)
  let Q (t : ℝ) := (Λ t).im * (t / K t)
  have hFint : IntervalIntegrable F MeasureTheory.volume 0 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)
    exact (hΛ.mul continuousOn_const).div (by unfold Z; fun_prop) (fun t _ => hden t)
  have hKc : Continuous K := by unfold K; fun_prop
  have hP : IntervalIntegrable P MeasureTheory.volume 0 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)
    exact ((Complex.continuous_im.comp_continuousOn hΛ).sub
      (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hΛ))).mul
      (continuous_const.div hKc (fun t => (hK t).ne')).continuousOn
  have hQ : IntervalIntegrable Q MeasureTheory.volume 0 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 2)
    exact (Complex.continuous_im.comp_continuousOn hΛ).mul
      (continuous_id.div hKc (fun t => (hK t).ne')).continuousOn
  have hIm (t : ℝ) : (F t).im = (1 / 2) * P t - Q t := by
    change (Λ t * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im = _
    rw [hF]
    simp [P, Q, s, Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re,
      Complex.div_ofReal_re, Complex.div_ofReal_im]
    ring
  change (∫ t in (0 : ℝ)..2, F t).im / Real.pi =
    (1 / (2 * Real.pi)) * (∫ t in (0 : ℝ)..2, P t) -
      (1 / Real.pi) * ∫ t in (0 : ℝ)..2, Q t
  have him := intervalIntegral.intervalIntegral_im hFint
  change (∫ t in (0:ℝ)..2, (F t).im) = (∫ t in (0:ℝ)..2, F t).im at him
  rw [← him]
  simp_rw [hIm]
  rw [intervalIntegral.integral_sub (hP.const_mul _) hQ, intervalIntegral.integral_const_mul]
  ring

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let η : ℝ → ℝ := fun x => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi
    let D := 2 / (9 * Real.exp 1) + 4 / (3 * Real.pi * Real.sqrt 3)
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (z < r → -(2/3) * Real.log 2 - D ≤ η z ∧ η z ≤ D) ∧
      (r < z → -D ≤ η z ∧ η z ≤ (1/3) * Real.log 2 + D) := by
  intro r s Z B η D x _hx
  obtain ⟨d, hB, hd, h0, hderiv, hslope, hsector⟩ :=
    MomentSearch.rakhmanov_triangle_phase_geometry N k hk hkN
  change ContinuousOn B (Set.Icc 0 2) at hB
  change (B 0).re = 0 at h0
  change ∀ t ∈ Set.Ioo 0 2, HasDerivAt (fun u => (B u).re) (d t) t at hderiv
  change ∀ t ∈ Set.Ioo 0 2, (B t).re / t ≤ d t at hslope
  change ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re at hsector
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkr : (0 : ℝ) ≤ k := by positivity
  have hkNr : (k : ℝ) < N := by exact_mod_cast hkN
  have hr : 0 < r := by
    unfold r
    apply Real.sqrt_pos.mpr
    rw [← div_pow, sub_pos]
    simpa using (sq_lt_sq₀ (div_nonneg hkr hNr.le) zero_le_one).mpr ((div_lt_one hNr).mpr hkNr)
  have side (hne : x ≠ r) :
      let y := 1 - x / r
      (0 < y → -(2/3) * Real.log 2 - D ≤ η x ∧ η x ≤ D) ∧
        (y < 0 → -D ≤ η x ∧ η x ≤ (1/3) * Real.log 2 + D) := by
    let y := 1-x/r
    have hy : y ≠ 0 := by
      intro he
      apply hne
      have he' : x / r = 1 := by unfold y at he; linarith
      exact (div_eq_one_iff_eq hr.ne').mp he'
    have ht := triangle_transform r x hr hne (fun t => Complex.log (1 + Complex.exp (-(B t))))
      (triangle_log_continuous B hB hsector)
    change η x = _ at ht
    rw [ht]
    exact triangle_half_integral_bounds B d hB hd h0 hderiv hslope hsector y hy
  constructor
  · intro hx
    exact (side hx.ne).1 (sub_pos.mpr ((div_lt_one hr).mpr hx))
  · intro hx
    exact (side hx.ne').2 (sub_neg.mpr ((one_lt_div hr).mpr hx))
