-- Prove2me | solution 1 for OAI.MetricKMedian.Analytic.P_nonneg_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:50:55.202078+00:00
-- url     : https://prove2.me/submissions/09be1625-f242-42b3-877b-77a357eff6ca

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

theorem P_nonneg_s53_oai (x : ℝ) : 0 ≤ P x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg ht.1 (Real.exp_pos _).le

end MetricKMedian.Analytic


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Analytic.P_nonneg_s53_oai := @OAI.MetricKMedian.Analytic.P_nonneg_s53_oai
