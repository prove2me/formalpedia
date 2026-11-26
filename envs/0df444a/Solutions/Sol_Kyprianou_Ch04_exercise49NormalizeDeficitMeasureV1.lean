-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49NormalizeDeficitMeasureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:43:21.950105+00:00
-- url     : https://prove2.me/submissions/4de4793f-2658-4cf7-92c3-3b7213982094

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Normalize the finite first-deficit measure. -/
theorem solution
    (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (nu mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnu : nu univ = ENNReal.ofReal rho)
    (hLaw : mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 + mu.conv nu) :
    ∃ eta : Measure ℝ, IsProbabilityMeasure eta ∧
      (∀ B : Set ℝ, (eta B).toReal = (nu B).toReal / rho) ∧
      mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
        ENNReal.ofReal rho • (mu.conv eta) := by
  have hr : ENNReal.ofReal rho ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr h0)
  have hrt : ENNReal.ofReal rho ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure nu := ⟨by rw [hnu]; exact lt_top_iff_ne_top.mpr hrt⟩
  let eta : Measure ℝ := (ENNReal.ofReal rho)⁻¹ • nu
  have hEta : IsProbabilityMeasure eta := ⟨by
    change (ENNReal.ofReal rho)⁻¹ * nu univ = 1
    rw [hnu, ENNReal.inv_mul_cancel hr hrt]⟩
  refine ⟨eta, hEta, ?_, ?_⟩
  · intro B
    change ((ENNReal.ofReal rho)⁻¹ * nu B).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal h0.le]
    ring
  · have hscale : ENNReal.ofReal rho • eta = nu := by
      change ENNReal.ofReal rho • ((ENNReal.ofReal rho)⁻¹ • nu) = nu
      rw [smul_smul, mul_comm, ENNReal.inv_mul_cancel hr hrt, one_smul]
    haveI : IsProbabilityMeasure eta := hEta
    rw [← hscale, Measure.conv_smul_right] at hLaw
    exact hLaw
