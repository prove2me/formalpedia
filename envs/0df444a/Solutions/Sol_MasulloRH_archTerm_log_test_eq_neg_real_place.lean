-- Prove2me | solution 1 for MasulloRH.archTerm_log_test_eq_neg_real_place
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:22:17.870175+00:00
-- url     : https://prove2.me/submissions/bc45f09f-22e1-42bf-a2e2-d6d4d14fdebb

import Definitions.Def_ConnesRZ_weil_defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib
import Theorems.Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloRH_realTraceIntegrand_integrable

set_option autoImplicit false

open ConnesRZ Complex MeasureTheory Set
open scoped FourierTransform SchwartzMap

private theorem arch_hat_scaled (g : ℝ → ℂ) (v : ℝ) :
    mellinHat g (1/2 + I * (↑(2 * Real.pi * v) : ℂ)) = 𝓕⁻ g v := by
  rw [mellinHat, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul, mul_comm (g t)]
  congr 2
  simp
  ring

private theorem arch_hat_unscaled (g : ℝ → ℂ) (r : ℝ) :
    mellinHat g (1/2 + I * r) = 𝓕⁻ g ((2 * Real.pi)⁻¹ * r) := by
  have hp : 2 * Real.pi ≠ 0 := by positivity
  convert arch_hat_scaled g ((2 * Real.pi)⁻¹ * r) using 3
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]

theorem arch_hat_int {g : ℝ → ℂ} (hg : ConnesRZ.IsTest g) :
    Integrable (fun r : ℝ => mellinHat g (1/2+I*r)) := by
  let f := hg.2.toSchwartzMap hg.1
  have hf : Integrable (𝓕⁻ g) := by
    have hi := (𝓕⁻ f).integrable (μ := volume)
    rw [SchwartzMap.fourierInv_coe] at hi
    exact hi
  simpa only [arch_hat_unscaled] using hf.comp_mul_left' (by positivity : (2*Real.pi)⁻¹ ≠ 0)

theorem arch_hat_moment {g : ℝ → ℂ} (hg : ConnesRZ.IsTest g) (k : ℕ) :
    Integrable (fun r : ℝ => |r|^k * ‖mellinHat g (1/2+I*r)‖) := by
  let f := hg.2.toSchwartzMap hg.1
  have hf : Integrable (fun v : ℝ => |v|^k * ‖𝓕⁻ g v‖) := by
    have hi := (𝓕⁻ f).integrable_pow_mul volume k
    rw [SchwartzMap.fourierInv_coe] at hi
    change Integrable (fun x : ℝ => ‖x‖^k * ‖𝓕⁻ g x‖) at hi
    simpa only [Real.norm_eq_abs] using hi
  let T : ℝ := 2*Real.pi
  have hp : 0<T := by dsimp [T]; positivity
  have h := (hf.comp_mul_left' (inv_ne_zero hp.ne')).const_mul (T^k)
  apply h.congr
  filter_upwards with r
  rw [arch_hat_unscaled]
  change T^k * (|T⁻¹ * r|^k * _) = |r|^k * _
  rw [abs_mul, abs_of_pos (inv_pos.mpr hp), mul_pow T⁻¹ _]
  rw [← mul_assoc, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hp.ne', one_pow, one_mul]

theorem arch_inversion_raw {g : ℝ → ℂ} (hg : ConnesRZ.IsTest g) (x : ℝ) :
    (∫ r : ℝ, mellinHat g (1/2+I*r) * Complex.exp (-I*r*x)) =
      (2 * (Real.pi : ℂ)) * g x := by
  let T : ℝ := 2 * Real.pi
  have hp : 0 < T := by dsimp [T]; positivity
  let H := fun v : ℝ => 𝓕⁻ g v * Complex.exp (-I * (↑(T*v):ℂ) * x)
  have hv : (∫ v, H v) = g x := by
    let f := hg.2.toSchwartzMap hg.1
    have hf : Integrable (𝓕 g) := (𝓕 f).integrable (μ := volume)
    have hfg : Integrable g := f.integrable
    rw [← hfg.fourier_fourierInv_eq hf (v := x) hg.1.continuous.continuousAt]
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with v
    dsimp only [H, T]
    rw [smul_eq_mul, mul_comm (𝓕⁻ g v)]
    congr 2
    push_cast
    ring
  calc
    _ = ∫ r : ℝ, H (T⁻¹*r) := by
      apply integral_congr_ae
      filter_upwards with r
      simp only [H, arch_hat_unscaled, ← mul_assoc T T⁻¹, mul_inv_cancel₀ hp.ne', one_mul]
      rfl
    _ = _ := by
      rw [Measure.integral_comp_mul_left, hv, inv_inv, abs_of_pos hp, Complex.real_smul]
      simp [T]

theorem arch_hat_continuous {g : ℝ → ℂ} (hg : ConnesRZ.IsTest g) :
    Continuous (fun r : ℝ => mellinHat g (1/2+I*r)) := by
  let f := hg.2.toSchwartzMap hg.1
  have hc := (𝓕⁻ f).continuous
  rw [SchwartzMap.fourierInv_coe] at hc
  change Continuous (𝓕⁻ g) at hc
  simp only [arch_hat_unscaled]
  exact hc.comp
    (continuous_const.mul continuous_id : Continuous (fun r : ℝ => (2*Real.pi)⁻¹*r))

theorem arch_inversion {g : ℝ → ℂ} (hg : ConnesRZ.IsTest g) (x : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ r : ℝ, mellinHat g (1/2+I*r) * Complex.exp (-I*r*x)) = g x := by
  rw [arch_inversion_raw hg x]
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : 2*Real.pi ≠ 0)
  field_simp
open MeasureTheory Set Filter Complex
private theorem arch_lorentz_pair {F g : ℝ → ℂ} (hF : Integrable F) (hm : Measurable F)
    (hinv : ∀ x : ℝ, (∫ r : ℝ, F r * exp (-I*r*x)) = (2*(Real.pi:ℂ))*g x)
    {c : ℝ} (hc : 0 < c) :
    (∫ r : ℝ, F r * ((c / (c^2+r^2) : ℝ) : ℂ)) =
      (Real.pi:ℂ) * ∫ x in Ioi (0:ℝ), (g x + g (-x)) * (Real.exp (-c*x) : ℂ) := by
  let J := fun (r x : ℝ) => F r *
    (exp ((-(c:ℂ)-I*r)*x) + exp ((-(c:ℂ)+I*r)*x))
  have hre (r : ℝ) : (-(c:ℂ)-I*r).re = -c ∧ (-(c:ℂ)+I*r).re = -c := by
    simp [Complex.mul_re]
  have hJ : Integrable (Function.uncurry J) (volume.prod (volume.restrict (Ioi 0))) := by
    have hh := hF.norm.mul_prod ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).mul_const 2)
    apply hh.mono'
    · apply Measurable.aestronglyMeasurable
      dsimp [Function.uncurry,J]; fun_prop
    · apply Filter.Eventually.of_forall
      rintro ⟨r,x⟩
      simp only [Function.uncurry_apply_pair,J,norm_mul]
      gcongr
      apply (norm_add_le _ _).trans
      simp [Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.add_re, mul_two]
  have hx (r : ℝ) : (∫ x in Ioi (0:ℝ), J r x) = 2 * (F r * ((c / (c^2+r^2) : ℝ) : ℂ)) := by
    dsimp only [J]
    have ha := (hre r).1.trans_lt (neg_lt_zero.mpr hc)
    have hb := (hre r).2.trans_lt (neg_lt_zero.mpr hc)
    rw [integral_const_mul, integral_add (integrableOn_exp_mul_complex_Ioi ha 0)
      (integrableOn_exp_mul_complex_Ioi hb 0), integral_exp_mul_complex_Ioi ha, integral_exp_mul_complex_Ioi hb]
    have hna : -(c:ℂ)-I*r ≠ 0 := fun e => by rw [e] at ha; exact lt_irrefl 0 ha
    have hnb : -(c:ℂ)+I*r ≠ 0 := fun e => by rw [e] at hb; exact lt_irrefl 0 hb
    have hden : (c:ℂ)^2+(r:ℂ)^2 ≠ 0 := by exact_mod_cast (by positivity : c^2+r^2 ≠ 0)
    push_cast
    simp only [mul_zero, exp_zero]
    field_simp
    ring_nf
    simp [I_sq]
  have hr (x : ℝ) : (∫ r : ℝ, J r x) =
      (2*(Real.pi:ℂ))*((g x + g (-x)) * (Real.exp (-c*x):ℂ)) := by
    let W := (Real.exp (-c*x):ℂ)
    have hes (r : ℝ) : J r x =
        (F r * exp (-I*r*x) + F r * exp (-I*r*(-x))) * W := by
      dsimp [J,W]
      rw [Complex.ofReal_exp]
      push_cast
      rw [show (-(c:ℂ)-I*r)*x=(-I*r*x)+(-c*x) by ring,
        show (-(c:ℂ)+I*r)*x=(-I*r*(-x))+(-c*x) by ring, exp_add, exp_add]
      ring
    have hi (v : ℝ) : Integrable (fun r : ℝ => F r * exp (-I*r*v)) := by
      apply hF.norm.mono' (by fun_prop)
      exact Filter.Eventually.of_forall fun r => by simp [norm_exp,Complex.mul_re]
    simp_rw [hes]
    rw [integral_mul_const, integral_add (hi x) (by simpa using hi (-x)), hinv x]
    simp_rw [← Complex.ofReal_neg, hinv (-x)]
    ring
  have he := integral_integral_swap (f := J) hJ
  simp_rw [hx, hr] at he
  rw [integral_const_mul, integral_const_mul] at he
  linear_combination he / 2

open Complex MeasureTheory Set Filter
open scoped Topology

private noncomputable def archZ (r : ℝ) : ℂ := 1/4 + Complex.I * r/2
private noncomputable def archTermN (n : ℕ) (r : ℝ) : ℂ := 1 / ((n:ℂ)+1) - 1 / ((n:ℂ)+ archZ r)
private noncomputable def archC (n : ℕ) : ℝ := 2*(n:ℝ)+1/2

private lemma archTermN_norm (n : ℕ) (r : ℝ) :
    ‖archTermN n r‖ ≤ (4 / ((n:ℝ)+1)^2) * (1 + |r|) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hzre : (archZ r).re = 1/4 := by simp [archZ]
  have h1 : 0 < (n:ℝ)+1 := by positivity
  have h0 : 0 < (n:ℝ)+1/4 := by positivity
  have hNr : (n:ℝ)+1/4 ≤ ‖(n:ℂ)+archZ r‖ := by
    simpa [hzre] using (Complex.re_le_norm ((n:ℂ)+archZ r))
  have hN : (n:ℂ)+archZ r ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le h0 hNr)
  have hN' : (n:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hnum : ‖archZ r - 1‖ ≤ 1 + |r| := by
    have he : archZ r - 1 = -(3/4) + Complex.I * r/2 := by unfold archZ; ring
    rw [he]
    apply (norm_add_le _ _).trans
    norm_num [norm_div, norm_mul, Real.norm_eq_abs]
    linarith [abs_nonneg r]
  have hrepr : archTermN n r = (archZ r - 1) / (((n:ℂ)+1)*((n:ℂ)+archZ r)) := by
    unfold archTermN
    field_simp
    ring
  rw [hrepr, norm_div, norm_mul, show ‖(n:ℂ)+1‖ = (n:ℝ)+1 by
    exact_mod_cast (Real.norm_of_nonneg h1.le)]
  apply (div_le_iff₀ (mul_pos h1 (lt_of_lt_of_le h0 hNr))).mpr
  calc _ ≤ 1+|r| := hnum
       _ ≤ 4 / ((n:ℝ)+1)^2 * (1+|r|) * (((n:ℝ)+1)*((n:ℝ)+1/4)) := by
         field_simp
         nlinarith [mul_nonneg hn (abs_nonneg r), mul_nonneg (sq_nonneg (n:ℝ)) (abs_nonneg r)]
       _ ≤ _ := by gcongr

private lemma archTermN_re (n : ℕ) (r : ℝ) : (archTermN n r).re =
    1 / ((n:ℝ)+1) - 2 * (archC n / ((archC n)^2 + r^2)) := by
  have h1 : 0 < (n:ℝ)+1 := by positivity
  have h2 : 0 < ((n:ℝ)+1/4)^2 + (r/2)^2 := by positivity
  have h3 : 0 < (2*(n:ℝ)+1/2)^2 + r^2 := by positivity
  have hAr : ((n:ℂ)+archZ r).re = (n:ℝ)+1/4 := by simp [archZ]
  have hAi : ((n:ℂ)+archZ r).im = r/2 := by simp [archZ]
  have hcast : 1/((n:ℂ)+1) = ((1/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; rfl
  rw [archTermN, hcast, Complex.sub_re, Complex.ofReal_re, one_div ((n:ℂ)+_),
    Complex.inv_re, Complex.normSq_apply, hAr, hAi]
  unfold archC
  rw [div_eq_mul_inv, div_eq_mul_inv]
  field_simp [← sq, h2.ne', h3.ne']
  ring

private theorem arch_digamma_interchange (F : ℝ → ℂ) (hF : Integrable F)
    (hw : Integrable (fun r : ℝ => (1+|r|) * ‖F r‖)) :
    HasSum (fun n : ℕ => ∫ r : ℝ, F r * ((archTermN n r).re : ℂ))
      (∫ r : ℝ, F r * (((Complex.digamma (archZ r)).re + Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
  let w := fun n : ℕ => 4 / ((n:ℝ)+1)^2
  let v := fun r : ℝ => (1+|r|) * ‖F r‖
  have hw' : Summable w := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide))
    simpa [w, div_eq_mul_inv] using h.mul_left 4
  apply hasSum_integral_of_dominated_convergence (fun n r => w n * v r)
  · intro n
    apply hF.aestronglyMeasurable.mul
    simp only [archTermN_re, archC]
    apply Measurable.aestronglyMeasurable
    exact Complex.measurable_ofReal.comp (by fun_prop)
  · intro n
    filter_upwards with r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ ‖F r‖ * ((4/((n:ℝ)+1)^2)*(1+|r|)) := mul_le_mul_of_nonneg_left
            ((Complex.abs_re_le_norm _).trans (archTermN_norm n r)) (norm_nonneg _)
         _ = _ := by dsimp [w,v]; ring
  · filter_upwards with r using hw'.mul_right (v r)
  · simp only [tsum_mul_right]
    exact hw.const_mul _
  · filter_upwards with r
    have hz : 0 < (archZ r).re := by norm_num [archZ]
    have H := Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
      (archZ r) hz
    simpa only [archTermN, Complex.add_re, Complex.ofReal_re] using
      (Complex.hasSum_ofReal.mpr (Complex.hasSum_re H)).mul_left (F r)

private lemma arch_shift_integral {G H : ℝ → ℂ} (hH : Integrable H) (hz : ∫ r, H r = 0) :
    (∫ r, G r + H r) = ∫ r, G r := by
  by_cases hG : Integrable G
  · rw [integral_add hG hH, hz, add_zero]
  · rw [integral_undef hG, integral_undef]
    intro h
    exact hG ((integrable_add_iff_integrable_left' hH).mp h)

private lemma arch_lorentz_int (F : ℝ → ℂ) (hF : Integrable F) {c : ℝ} (hc : 0 < c) :
    Integrable (fun r : ℝ => F r * ((c / (c^2+r^2) : ℝ):ℂ)) := by
  apply (hF.norm.mul_const (1/c)).mono'
  · exact hF.aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with r
    have hden : 0 < c^2 + r^2 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (div_le_div_iff₀ hden hc).mpr
    nlinarith [sq_nonneg r]

private theorem arch_digamma_sum (F : ℝ → ℂ) (hF : Integrable F)
    (hw : Integrable (fun r : ℝ => (1+|r|) * ‖F r‖)) (hzero : (∫ r, F r) = 0) :
    HasSum (fun n : ℕ => -2 * ∫ r : ℝ, F r * ((archC n / ((archC n)^2 + r^2) : ℝ) : ℂ))
      (∫ r : ℝ, F r * (((Complex.digamma (archZ r)).re - Real.log Real.pi : ℝ) : ℂ)) := by
  let C : ℂ := (Real.eulerMascheroniConstant : ℂ) + Real.log Real.pi
  have hshift := arch_shift_integral (G := fun r => F r *
    (((Complex.digamma (archZ r)).re - Real.log Real.pi : ℝ):ℂ))
    (hF.mul_const C) (by simp [integral_mul_const, hzero])
  have heq : (∫ r : ℝ, F r * (((Complex.digamma (archZ r)).re + Real.eulerMascheroniConstant : ℝ) : ℂ)) =
      (∫ r : ℝ, F r * (((Complex.digamma (archZ r)).re - Real.log Real.pi : ℝ):ℂ)) := by
    rw [← hshift]
    congr 1
    ext r
    dsimp [C]
    push_cast
    ring
  rw [← heq]
  apply (arch_digamma_interchange F hF hw).congr_fun
  intro n
  let c := archC n
  have hc : 0 < c := by dsimp [c, archC]; positivity
  have hi := arch_lorentz_int F hF hc
  simp_rw [archTermN_re]
  have hcong (r : ℝ) : F r * ((1/((n:ℝ)+1) - 2*(c/(c^2+r^2)) : ℝ) : ℂ) =
      F r * ((1/((n:ℝ)+1) : ℝ) : ℂ) - 2 * (F r * ((c/(c^2+r^2) : ℝ) : ℂ)) := by push_cast; ring
  symm
  change (∫ r, F r * ((1/((n:ℝ)+1) - 2*(c/(c^2+r^2)) : ℝ) : ℂ)) = _
  simp_rw [hcong]
  rw [integral_sub (hF.mul_const _) (hi.const_mul 2), integral_mul_const, hzero, integral_const_mul]
  ring

open MeasureTheory Set Filter
open scoped Topology

namespace MasulloRH

private theorem kernel_log_change (x : ℝ) (hx : 0 < x) :
    Real.exp x * (Real.sqrt (Real.exp x) / (Real.exp x ^ 2 - 1)) =
      Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) := by
  let y := Real.exp (x / 2)
  have hy : 1 < y := Real.one_lt_exp_iff.mpr (by positivity)
  have he : Real.exp x = y^2 := by
    dsimp [y]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h₁ : Real.exp (-x/2) = y⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have h₂ : Real.exp (-2*x) = (y^4)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    congr 1
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, h₁, h₂, Real.sqrt_sq (by positivity : 0 ≤ y)]
  have hn : y ≠ 0 := by linarith
  have h4 : 1 < y^4 := one_lt_pow₀ hy (by decide)
  field_simp


theorem arch_log_coordinate (φ : ℝ → ℂ) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) =
      ∫ x in Ioi (0 : ℝ), ((φ ∘ Real.exp) x + (φ ∘ Real.exp) (-x)) *
        ((Real.exp (-x/2) / (1 - Real.exp (-2*x)) : ℝ) : ℂ) := by
  have h := integral_comp_exp_Ioi (realTraceIntegrand φ) 0
  rw [Real.exp_zero] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [realTraceIntegrand, Function.comp_apply, Real.exp_neg, Complex.real_smul]
  rw [← kernel_log_change x hx, Complex.ofReal_mul]
  ring

end MasulloRH

namespace MasulloRH

private theorem arch_log_integrable {φ : ℝ → ℂ} (hi : IntegrableOn (realTraceIntegrand φ) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => ((φ ∘ Real.exp) x + (φ ∘ Real.exp) (-x)) *
      ((Real.exp (-x/2) / (1 - Real.exp (-2*x)) : ℝ) : ℂ)) (Ioi 0) := by
  have he := (integrableOn_comp_exp_Ioi (realTraceIntegrand φ) 0).mpr
    (by simpa only [Real.exp_zero] using hi)
  apply he.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [realTraceIntegrand, Function.comp_apply, Real.exp_neg, Complex.real_smul]
  rw [← kernel_log_change x hx, Complex.ofReal_mul]
  ring

end MasulloRH

open MeasureTheory Set Filter
open scoped Topology


private theorem arch_geometric {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-archC n*x)) (Real.exp (-x/2)/(1-Real.exp (-2*x))) := by
  have h := hasSum_geometric_of_lt_one (Real.exp_pos (-2*x)).le
    (Real.exp_lt_one_iff.mpr (show -2*x < 0 by linarith))
  have he (n : ℕ) : Real.exp (-archC n*x) = Real.exp (-x/2) * Real.exp (-2*x)^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [archC]
    ring
  simpa only [he, div_eq_mul_inv] using h.mul_left (Real.exp (-x/2))

private theorem arch_physical_sum (g : ℝ → ℂ) (hg : Continuous g)
    (hi : IntegrableOn (fun x : ℝ => (g x + g (-x)) *
      ((Real.exp (-x/2)/(1-Real.exp (-2*x)) : ℝ) : ℂ)) (Ioi 0)) :
    HasSum (fun n : ℕ => ∫ x in Ioi (0 : ℝ), (g x + g (-x))*(Real.exp (-archC n*x) : ℂ))
      (∫ x in Ioi (0 : ℝ), (g x + g (-x))*((Real.exp (-x/2)/(1-Real.exp (-2*x)) : ℝ) : ℂ)) := by
  let u := fun x : ℝ => g x + g (-x)
  let W := fun x : ℝ => Real.exp (-x/2)/(1-Real.exp (-2*x))
  have hue : Continuous u := hg.add (hg.comp continuous_neg)
  refine hasSum_integral_of_dominated_convergence (fun n x => ‖u x‖ * Real.exp (-archC n*x)) ?_ ?_ ?_ ?_ ?_
  · intro n
    apply Continuous.aestronglyMeasurable
    exact hue.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  · intro n
    exact ae_of_all _ fun x => by
      change ‖u x * (Real.exp (-archC n*x) : ℂ)‖ ≤ ‖u x‖ * _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact ((arch_geometric hx).mul_left ‖u x‖).summable
  · apply hi.norm.congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hpos : 0 ≤ W x := by
      apply div_nonneg (Real.exp_pos _).le
      apply sub_nonneg.mpr
      exact Real.exp_le_one_iff.mpr (by have : 0 < x := hx; linarith)
    rw [((arch_geometric hx).mul_left ‖u x‖).tsum_eq]
    change ‖u x * (W x : ℂ)‖ = ‖u x‖ * W x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact (Complex.hasSum_ofReal.mpr (arch_geometric hx)).mul_left (u x)
namespace MasulloRH

private theorem log_test {φ : ℝ → ℂ} (h : IsRationalTraceTest φ) :
    ConnesRZ.IsTest (φ ∘ Real.exp) := by
  refine ⟨h.1.comp Real.contDiff_exp, HasCompactSupport.of_support_subset_isCompact
    (K := Real.log '' tsupport φ) (h.2.1.image_of_continuousOn ?_) ?_⟩
  · exact Real.continuousOn_log.mono (fun t ht => (h.2.2.1 ht).ne')
  · intro t ht
    exact ⟨Real.exp t, subset_tsupport φ ht, Real.log_exp t⟩

end MasulloRH
open MasulloRH ConnesRZ Complex MeasureTheory Set

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    archTerm (φ ∘ Real.exp) = -(∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) := by
  let g := φ ∘ Real.exp
  let F := fun r : ℝ => mellinHat g (1/2+I*r)
  have hg : IsTest g := log_test hφ
  have hf := arch_hat_int hg
  have hzero : (∫ r, F r) = 0 := by
    simpa [F,g,hφ.2.2.2] using arch_inversion_raw hg 0
  have hw : Integrable (fun r : ℝ => (1+|r|) * ‖F r‖) := by
    simpa only [Pi.add_apply, F, add_mul, one_mul, pow_one, Pi.add_def] using hf.norm.add (arch_hat_moment hg 1)
  have hd := arch_digamma_sum F hf hw hzero
  have hmode (n : ℕ) := arch_lorentz_pair hf (arch_hat_continuous hg).measurable
    (arch_inversion_raw hg) (c := archC n) (by unfold archC; positivity)
  have hi := arch_log_integrable (realTraceIntegrand_integrable φ hφ)
  have hp := (arch_physical_sum g hg.1.continuous hi).mul_left (-2*(Real.pi:ℂ))
  have hh := hp.unique (hd.congr_fun (fun n => by
    dsimp only [F]
    rw [hmode]
    ring))
  change (1/(2*(Real.pi:ℂ))) * (∫ r : ℝ, F r * (((Complex.digamma (archZ r)).re - Real.log Real.pi : ℝ):ℂ)) = _
  rw [arch_log_coordinate, ← hh]
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp only [g]
  field_simp
  ring_nf
