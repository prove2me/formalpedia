-- Prove2me | solution 1 for OAI.MetricKMedian.Analytic.m_nonneg_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:52:03.532986+00:00
-- url     : https://prove2.me/submissions/c1822fd5-3d49-469b-96e7-0c7d92912e53

import Mathlib
import Definitions.Def_OAIQ053K000

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem m_nonneg_s53_oai (x : ℝ) : 0 ≤ m x := by
  have h : 0 ≤ ∫ t : ℝ in 0..1,
      (1 - Real.exp (-t * x) - x * (t * Real.exp (-t * x))) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t * x))
      (Real.exp_pos (-t * x)).le
    have hexp : Real.exp (t * x) * Real.exp (-t * x) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 2
      all_goals try with_reducible_and_instances rfl
      ring
    rw [hexp] at he
    nlinarith
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub hi ((texp_integrable x).const_mul x),
    intervalIntegral.integral_const_mul] at h
  unfold m A P
  linarith

end MetricKMedian.Analytic


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Analytic.m_nonneg_s53_oai := @OAI.MetricKMedian.Analytic.m_nonneg_s53_oai
