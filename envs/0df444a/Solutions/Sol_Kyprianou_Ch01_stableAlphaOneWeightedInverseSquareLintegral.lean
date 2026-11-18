-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneWeightedInverseSquareLintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:31:57.559981+00:00
-- url     : https://prove2.me/submissions/25f04e46-efc7-4ce9-8fc0-d60ab503e5aa

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneInverseSquareLintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! Move the nonnegative cosine deficit outside the Tonelli-side Laplace integral. -/
theorem solution
    (x : ℝ) (hx : 0 < x) :
    (∫⁻ a in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      ENNReal.ofReal ((1 - Real.cos x) / x ^ 2) := by
  have hc : 0 ≤ 1 - Real.cos x :=
    sub_nonneg.mpr (Real.cos_le_one x)
  have hf : Measurable (fun a : ℝ =>
      ENNReal.ofReal (a * Real.exp (-(a * x)))) := by
    fun_prop
  have hfac :
      (∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      (∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.exp (-(a * x)))) *
          ENNReal.ofReal (1 - Real.cos x) := by
    calc
      _ = ∫⁻ a in Ioi (0 : ℝ),
          ENNReal.ofReal (a * Real.exp (-(a * x))) *
            ENNReal.ofReal (1 - Real.cos x) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact ENNReal.ofReal_mul
          (mul_nonneg ha.le (Real.exp_pos _).le)
      _ = (∫⁻ a in Ioi (0 : ℝ),
          ENNReal.ofReal (a * Real.exp (-(a * x)))) *
          ENNReal.ofReal (1 - Real.cos x) := by
        exact lintegral_mul_const _ hf
  rw [hfac]
  have hchange :
      (∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.exp (-(a * x)))) =
      (∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.exp (-(x * a)))) := by
    apply lintegral_congr_ae
    filter_upwards [] with a
    rw [mul_comm a x]
  rw [hchange, Kyprianou.Ch01.stableAlphaOneInverseSquareLintegral x hx]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (x ^ 2)⁻¹)]
  congr 1
  ring
