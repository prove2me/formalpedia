-- Prove2me | solution 1 for LinParamBandits.UEGeneral.exp_ineq_ratios
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:00:42.62136+00:00
-- url     : https://prove2.me/submissions/8295f8f0-7e06-43f1-880a-54c6b7682f62

import Mathlib

open MeasureTheory ProbabilityTheory

namespace UEGenB3Aux

/-- Completing the square: `a γ - c γ²/2 = a²/(2c) - (c/2)(γ - a/c)²`. -/
lemma complete_sq (a c γ : ℝ) (hc : 0 < c) :
    a * γ - c * γ ^ 2 / 2 = a ^ 2 / (2 * c) + (-(c / 2) * (γ - a / c) ^ 2) := by
  field_simp
  ring

lemma integrable_quad (a c : ℝ) (hc : 0 < c) :
    Integrable (fun γ : ℝ => Real.exp (a * γ - c * γ ^ 2 / 2)) := by
  have h := ((integrable_exp_neg_mul_sq (b := c / 2) (by positivity)).comp_sub_right (a / c)).const_mul
    (Real.exp (a ^ 2 / (2 * c)))
  refine h.congr (Filter.Eventually.of_forall (fun γ => ?_))
  simp only
  rw [complete_sq a c γ hc, Real.exp_add]

lemma integral_quad (a c : ℝ) (hc : 0 < c) :
    ∫ γ : ℝ, Real.exp (a * γ - c * γ ^ 2 / 2) =
      Real.exp (a ^ 2 / (2 * c)) * Real.sqrt (Real.pi / (c / 2)) := by
  have : (fun γ : ℝ => Real.exp (a * γ - c * γ ^ 2 / 2)) =
      fun γ => Real.exp (a ^ 2 / (2 * c)) * (fun x => Real.exp (-(c / 2) * x ^ 2)) (γ - a / c) := by
    funext γ
    rw [complete_sq a c γ hc, Real.exp_add]
  rw [this, integral_const_mul, integral_sub_right_eq_self (fun x => Real.exp (-(c / 2) * x ^ 2)),
    integral_gaussian]

end UEGenB3Aux

open UEGenB3Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B) (hB0 : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hexp : ∀ γ : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2)) ∂P ≤ 1)
    (ζ : ℝ) (hζ : Real.sqrt 2 ≤ ζ) (y : ℝ) (hy : 0 < y) :
    P {ω | ζ * Real.sqrt ((B ω ^ 2 + y) * (1 + 1 / 2 * Real.log (1 + B ω ^ 2 / y))) ≤ |A ω|} ≤
      ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by
  -- the Gaussian mixing density `k exp(-y γ²/2)` of `N(0, 1/y)`
  set s := Real.sqrt (Real.pi / (y / 2)) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set k := 1 / s with hk
  have hkpos : 0 < k := by positivity
  -- the mixture `G ω = ∫ k exp(-yγ²/2) exp(γ A - γ² B²/2) dγ`
  set G : Ω → ℝ := fun ω => k * (Real.exp (A ω ^ 2 / (2 * (B ω ^ 2 + y))) *
    Real.sqrt (Real.pi / ((B ω ^ 2 + y) / 2))) with hG
  have hpt : ∀ ω, ENNReal.ofReal (G ω) = ∫⁻ γ : ℝ,
      ENNReal.ofReal (k * Real.exp (-(y / 2) * γ ^ 2)) *
        ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2)) := by
    intro ω
    have hc : 0 < B ω ^ 2 + y := by positivity
    have heq : ∀ γ : ℝ, ENNReal.ofReal (k * Real.exp (-(y / 2) * γ ^ 2)) *
        ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2)) =
        ENNReal.ofReal (k * Real.exp (A ω * γ - (B ω ^ 2 + y) * γ ^ 2 / 2)) := by
      intro γ
      rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
      congr 3
      ring
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_quad _ _ hc).const_mul k)
      (Filter.Eventually.of_forall (fun γ => by positivity)), integral_const_mul, integral_quad _ _ hc]
  -- `E[G] ≤ 1` by Tonelli and the hypothesis
  have hmeasF : Measurable (Function.uncurry fun (ω : Ω) (γ : ℝ) =>
      ENNReal.ofReal (k * Real.exp (-(y / 2) * γ ^ 2)) *
        ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2))) := by
    fun_prop
  have hEG : ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤ 1 := by
    simp_rw [hpt]
    rw [lintegral_lintegral_swap hmeasF.aemeasurable]
    calc ∫⁻ γ : ℝ, ∫⁻ ω, ENNReal.ofReal (k * Real.exp (-(y / 2) * γ ^ 2)) *
          ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2)) ∂P
        = ∫⁻ γ : ℝ, ENNReal.ofReal (k * Real.exp (-(y / 2) * γ ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * A ω - γ ^ 2 * B ω ^ 2 / 2)) ∂P := by
          congr 1; funext γ
          rw [lintegral_const_mul]
          apply ENNReal.measurable_ofReal.comp
          apply Real.measurable_exp.comp
          exact (measurable_const.mul hA).sub ((measurable_const.mul (hB.pow_const 2)).div_const 2)
      _ ≤ ∫⁻ γ : ℝ, ENNReal.ofReal (k * Real.exp (-(y / 2) * γ ^ 2)) * 1 := by
          gcongr with γ
          exact hexp γ
      _ = ENNReal.ofReal (∫ γ : ℝ, k * Real.exp (-(y / 2) * γ ^ 2)) := by
          simp only [mul_one]
          rw [ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq (by positivity)).const_mul k)
            (Filter.Eventually.of_forall (fun γ => by positivity))]
      _ = 1 := by
          rw [integral_const_mul, integral_gaussian, ← hs, hk, one_div, inv_mul_cancel₀ hspos.ne',
            ENNReal.ofReal_one]
  -- on the event, `G ≥ exp(ζ²/2)`
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζ
  have hζ2 : 2 ≤ ζ ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hsub : {ω | ζ * Real.sqrt ((B ω ^ 2 + y) * (1 + 1 / 2 * Real.log (1 + B ω ^ 2 / y))) ≤ |A ω|} ⊆
      {ω | ENNReal.ofReal (Real.exp (ζ ^ 2 / 2)) ≤ ENNReal.ofReal (G ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply ENNReal.ofReal_le_ofReal
    set c := B ω ^ 2 + y with hcdef
    have hc : 0 < c := by positivity
    set L := Real.log (c / y) with hL
    have hcy : 1 ≤ c / y := by rw [le_div_iff₀ hy]; nlinarith [sq_nonneg (B ω)]
    have hL0 : 0 ≤ L := Real.log_nonneg hcy
    have hL' : Real.log (1 + B ω ^ 2 / y) = L := by
      rw [hL]; congr 1; rw [hcdef, add_div, div_self hy.ne', add_comm]
    rw [hL'] at hω
    have hX : 0 ≤ c * (1 + 1 / 2 * L) := by positivity
    have hsq : ζ ^ 2 * (c * (1 + 1 / 2 * L)) ≤ A ω ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hω 2
      rw [mul_pow, Real.sq_sqrt hX, sq_abs] at h1
      exact h1
    have hA2 : ζ ^ 2 / 2 * (1 + 1 / 2 * L) ≤ A ω ^ 2 / (2 * c) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    -- `G ω = √(y/c) exp(A²/(2c)) = exp(A²/(2c) - L/2)`
    have hsqrt : Real.sqrt (Real.pi / (c / 2)) = s * Real.sqrt (y / c) := by
      rw [hs, ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    have hyc : Real.sqrt (y / c) = Real.exp (-(L / 2)) := by
      have h1 : y / c = Real.exp (-(L / 2)) ^ 2 := by
        rw [sq, ← Real.exp_add, show -(L / 2) + -(L / 2) = -L by ring, Real.exp_neg, hL,
          Real.exp_log (by positivity), inv_div]
      rw [h1, Real.sqrt_sq (Real.exp_pos _).le]
    have hGeq : G ω = Real.exp (A ω ^ 2 / (2 * c) - L / 2) := by
      simp only [hG]
      rw [← hcdef, hsqrt, hyc, hk, sub_eq_add_neg, Real.exp_add]
      field_simp
    rw [hGeq, Real.exp_le_exp]
    nlinarith
  -- Markov's inequality
  have hGm : AEMeasurable (fun ω => ENNReal.ofReal (G ω)) P := by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    simp only [hG]
    apply measurable_const.mul
    apply Measurable.mul
    · exact Real.measurable_exp.comp ((hA.pow_const 2).div (measurable_const.mul ((hB.pow_const 2).add_const y)))
    · exact (measurable_const.div (((hB.pow_const 2).add_const y).div_const 2)).sqrt
  have hM := mul_meas_ge_le_lintegral₀ hGm (ENNReal.ofReal (Real.exp (ζ ^ 2 / 2)))
  have hpos : ENNReal.ofReal (Real.exp (ζ ^ 2 / 2)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have hfin : ENNReal.ofReal (Real.exp (ζ ^ 2 / 2)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc P {ω | ζ * Real.sqrt ((B ω ^ 2 + y) * (1 + 1 / 2 * Real.log (1 + B ω ^ 2 / y))) ≤ |A ω|}
      ≤ P {ω | ENNReal.ofReal (Real.exp (ζ ^ 2 / 2)) ≤ ENNReal.ofReal (G ω)} := measure_mono hsub
    _ ≤ 1 / ENNReal.ofReal (Real.exp (ζ ^ 2 / 2)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin), mul_comm]
        exact hM.trans hEG
    _ = ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by
        rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_div]
