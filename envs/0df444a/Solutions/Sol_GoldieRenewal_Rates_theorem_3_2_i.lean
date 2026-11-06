-- Prove2me | solution 1 for GoldieRenewal.Rates.theorem_3_2_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:46:12.821615+00:00
-- url     : https://prove2.me/submissions/7b2c86c6-e8df-430a-aaf8-fad4fe2fc568
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Theorems.Thm_GoldieRenewal_Rates_eq_9_24
import Theorems.Thm_GoldieRenewal_Rates_theorem_9_6
import Theorems.Thm_GoldieRenewal_Rates_r1_bounded_tauberian
import Theorems.Thm_GoldieRenewal_Rates_contour_convolution_identity

open MeasureTheory ProbabilityTheory Complex Filter Asymptotics Topology
open GoldieRenewal.Rates

lemma smoothingKernel_eq_indicator (b : ℝ) :
    smoothingKernel b = Set.indicator (Set.Ioi 0) (fun t => b * Real.exp (-(b * t))) := by
  funext t
  simp only [smoothingKernel, Set.indicator, Set.mem_Ioi]

lemma smoothingKernel_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => (smoothingKernel b t : ℂ)) := by
  have h : Integrable (smoothingKernel b) := by
    rw [smoothingKernel_eq_indicator, integrable_indicator_iff measurableSet_Ioi]
    have := (exp_neg_integrableOn_Ioi 0 hb).const_mul b
    simp only [neg_mul] at this; exact this
  exact h.ofReal

lemma smoothingKernel_fourier (b : ℝ) (hb : 0 < b) (ξ : ℝ) :
    fourierTransform (fun t : ℝ => (smoothingKernel b t : ℂ)) ξ = b / (b - I * ξ) := by
  unfold fourierTransform
  have hfun : (fun t : ℝ => Complex.exp (I * (ξ : ℂ) * t) * (smoothingKernel b t : ℂ)) =
      Set.indicator (Set.Ioi 0) (fun t : ℝ => (b : ℂ) * Complex.exp ((I * ξ - b) * t)) := by
    funext t
    simp only [smoothingKernel, Set.indicator, Set.mem_Ioi]
    split_ifs
    · push_cast
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    · simp
  rw [hfun, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simp [hb]) 0]
  have hne : (I * (ξ : ℂ) - b) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne2 : ((b : ℂ) - I * ξ) ≠ 0 := by
    intro h; apply hne; linear_combination -h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0)) :
    ExpansionPos P M R κ β := by
  intro z w hC
  have hb : 0 < β + 1 := by linarith
  have h24 := eq_9_24 P M R hM hR hM_nonneg h_indep κ β hκ hβ h_2_3 h_3_3 h_3_4 h_stone h_3_7
    (β + 1) (by linarith) z w hC
  obtain ⟨hmeas, hbdd, A, x₀, htaub⟩ := r1_bounded_tauberian P M R hM hR hM_nonneg h_indep κ β
    hκ hβ h_2_3 h_3_3 h_3_4 h_stone h_3_7 z w hC
  have hident := contour_convolution_identity P M R hM hR hM_nonneg h_indep κ β
    hκ hβ h_2_3 h_3_3 h_3_4 h_stone h_3_7 z w hC
  set f : ℝ → ℝ := fun t => (r1Fun P M R κ z w t).re with hf
  set b : ℝ := β + 1 with hbdef
  -- the kernel
  have hKint := smoothingKernel_integrable b hb
  have hKne : ∀ ξ : ℝ, fourierTransform (fun t : ℝ => (smoothingKernel b t : ℂ)) ξ ≠ 0 := by
    intro ξ
    rw [smoothingKernel_fourier b hb ξ]
    have hne2 : ((b : ℂ) - I * ξ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    exact div_ne_zero (by exact_mod_cast hb.ne') hne2
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hw_holo : DifferentiableOn ℂ (fun ζ : ℂ => 1 - I * ζ / b)
      {ζ : ℂ | -(β + 1) < ζ.im ∧ ζ.im < 0} := by fun_prop
  have hw_deriv : ∀ ζ : ℂ, -(β + 1) < ζ.im → ζ.im < 0 →
      ‖deriv (fun ζ : ℂ => 1 - I * ζ / b) ζ‖ < (2 / b) * (1 + ‖ζ‖) ^ ((1 : ℝ) - 1) := by
    intro ζ _ _
    have hd : HasDerivAt (fun ζ : ℂ => 1 - I * ζ / b) (-(I * 1 / b)) ζ :=
      (((hasDerivAt_id ζ).const_mul I).div_const (b : ℂ)).const_sub 1
    rw [hd.deriv]
    simp only [sub_self, Real.rpow_zero, mul_one, norm_neg, norm_div, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    rw [div_lt_div_iff_of_pos_right hb]
    norm_num
  have hw_lim : ∀ ξ : ℝ, Tendsto (fun η : ℝ => (fun ζ : ℂ => 1 - I * ζ / b) ((ξ : ℂ) - I * (η : ℂ)))
      (𝓝[>] 0) (𝓝 (1 / fourierTransform (fun t : ℝ => (smoothingKernel b t : ℂ)) ξ)) := by
    intro ξ
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun η : ℝ => (fun ζ : ℂ => 1 - I * ζ / b) ((ξ : ℂ) - I * (η : ℂ))) := by
      fun_prop
    have := hc.tendsto 0
    convert this using 2
    rw [smoothingKernel_fourier b hb ξ]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    field_simp
  have htaub' : ∀ x : ℝ, x₀ < x → ∀ y : ℝ, 0 ≤ y → y ≤ Real.exp (-(β * x) / (1 + 1)) →
      f x - f (x + y) ≤ A * Real.exp (-(β * x) / (1 + 1)) := by
    intro x hx y hy hy'
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h2] at hy' ⊢
    exact htaub x hx y hy hy'
  have hconv : (fun x : ℝ => ∫ u : ℝ, (smoothingKernel b (x - u) : ℂ) * (f u : ℂ)) =O[atTop]
      (fun x : ℝ => Real.exp (-(β * x))) := by
    have heq : (fun x : ℝ => ∫ u : ℝ, (smoothingKernel b (x - u) : ℂ) * (f u : ℂ)) =
        fun x : ℝ => ((∫ u : ℝ, smoothingKernel b (x - u) * f u : ℝ) : ℂ) := by
      funext x
      rw [← integral_complex_ofReal]
      congr 1
      funext u
      push_cast
      rfl
    rw [heq]
    refine Asymptotics.IsBigO.of_norm_left ?_
    simp only [Complex.norm_real]
    exact h24.isBigO.norm_left
  have h96 := theorem_9_6 (fun t : ℝ => (smoothingKernel b t : ℂ)) hKint hKne 1 (β + 1) (2 / b)
    (by norm_num) hb (fun ζ : ℂ => 1 - I * ζ / b) hw_holo hw_deriv hw_lim β hβ (by linarith)
    f hmeas hbdd A x₀ htaub' hconv
  have hcomp := (h96.comp_tendsto Real.tendsto_log_atTop).neg_left
  refine hcomp.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos ht
    simp only [Function.comp_apply, hf, r1Fun, if_pos hlog, hident (Real.log t)]
    simp only [GoldieRenewal.Implicit.rFun, Real.exp_log ht0, contourTermPos]
    rw [Real.rpow_def_of_pos ht0]
    have h2pi : (1 / (2 * Real.pi : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
    rw [h2pi, Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re,
      Complex.re_ofReal_mul, mul_comm (Real.log t) κ]
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
