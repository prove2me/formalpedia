-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineLintegralEqualsRational
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:36:39.359651+00:00
-- url     : https://prove2.me/submissions/ca6201f9-1bff-498e-b281-f5086b4258c6

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceTonelliSwap
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneWeightedInverseSquareLintegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceDeficitLintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! Tonelli identifies the two nonnegative scalar integrals exactly. -/
theorem solution :
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)) =
    (∫⁻ a in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 + a ^ 2)⁻¹)) := by
  have hLeft :
      (∫⁻ x in Ioi (0 : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Kyprianou.Ch01.stableAlphaOneWeightedInverseSquareLintegral x hx
  have hRight :
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      (∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 + a ^ 2)⁻¹)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact Kyprianou.Ch01.stableAlphaOneLaplaceDeficitLintegral a ha
  exact hLeft.symm.trans
    (Kyprianou.Ch01.stableAlphaOneLaplaceTonelliSwap.trans hRight)
