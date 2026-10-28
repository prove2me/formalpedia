-- Prove2me | solution 1 for OAI.MetricKMedian.Analytic.P_le_half_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:48:53.487142+00:00
-- url     : https://prove2.me/submissions/93278e54-b405-4a28-9e1e-784eb739e138

import Mathlib
import Definitions.Def_OAIQ035K000

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
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

theorem P_antitone : Antitone P := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num) (texp_integrable y) (texp_integrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ ht.1
  apply Real.exp_le_exp.mpr
  nlinarith [ht.1]

theorem P_le_half_s35_oai {x : ℝ} (hx : 0 ≤ x) : P x ≤ 1 / 2 := by
  simpa using P_antitone hx

end MetricKMedian.Analytic


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Analytic.P_le_half_s35_oai := @OAI.MetricKMedian.Analytic.P_le_half_s35_oai
