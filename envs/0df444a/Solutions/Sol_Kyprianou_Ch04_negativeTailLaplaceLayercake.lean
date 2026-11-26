-- Prove2me | solution 1 for Kyprianou.Ch04.negativeTailLaplaceLayercake
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:11.123116+00:00
-- url     : https://prove2.me/submissions/fce076f2-701d-4ce5-8471-21026be5e815

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_laplace_layercake
import Theorems.Thm_AvramDividend_Classical_negative_jump_tail_pushforward
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted negative Lévy tails equal the integrated normalized jump deficit. -/
theorem solution (nu : Measure ℝ) (hnu : nu (Ici 0) = 0) (a : ℝ) (ha : 0 < a) :
    (∫⁻ t in Ioi (0 : ℝ), nu (Iio (-t)) * ENNReal.ofReal (Real.exp (-a*t))) =
      ∫⁻ y : ℝ, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂nu := by
  let R : ℝ → NNReal := fun y => Real.toNNReal (-y)
  let Q := nu.map R
  let G : NNReal → ENNReal := fun z => ENNReal.ofReal ((1-Real.exp (-a*(z:ℝ)))/a)
  have hm : Measurable G := by fun_prop
  have hR : Measurable R := by fun_prop
  have hI (z : NNReal) : (∫ t in (0 : ℝ)..(z : ℝ), Real.exp (-a*t)) =
      (1-Real.exp (-a*(z:ℝ)))/a := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr ha.ne'), integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp [ha.ne']
    <;> ring
  have h := AvramDividend.Classical.positive_jump_tail_laplace_layercake Q a ha
  simp_rw [hI] at h
  change (∫⁻ z, G z ∂Q) = _ at h
  rw [lintegral_map hm hR] at h
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), Q {z : NNReal | t < (z : ℝ)} * ENNReal.ofReal (Real.exp (-a*t)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [show Q {z : NNReal | t < (z : ℝ)} = nu (Iio (-t)) from
        AvramDividend.Classical.negative_jump_tail_pushforward nu t ht]
    _ = ∫⁻ y, G (R y) ∂nu := h.symm
    _ = _ := by
      have hae : ∀ᵐ y ∂nu, y < 0 := by
        rw [ae_iff]
        simpa only [not_lt,← mem_Ici, Set.setOf_mem_eq] using hnu
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      simp only [G,R,Real.coe_toNNReal _ (neg_nonneg.mpr hy.le),mul_neg,neg_mul,neg_neg]
