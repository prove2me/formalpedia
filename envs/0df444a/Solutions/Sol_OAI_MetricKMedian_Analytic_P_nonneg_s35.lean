-- Prove2me | solution 1 for OAI.MetricKMedian.Analytic.P_nonneg_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:48:54.440884+00:00
-- url     : https://prove2.me/submissions/99d1291e-1c79-45fe-b729-93255fb04ff2

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

theorem P_nonneg_s35_oai (x : ℝ) : 0 ≤ P x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg ht.1 (Real.exp_pos _).le

end MetricKMedian.Analytic


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Analytic.P_nonneg_s35_oai := @OAI.MetricKMedian.Analytic.P_nonneg_s35_oai
