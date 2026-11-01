-- Prove2me | solution 1 for OAI.MetricKMedian.approximationFactors_nonempty_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:49:04.319816+00:00
-- url     : https://prove2.me/submissions/7d09bcf3-02a9-41c7-b875-74e1fe66e352

import Mathlib
import Definitions.Def_KMedianThreshold
import Theorems.Thm_OAI_MetricKMedian_factor_above_threshold_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Analysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian

theorem approximationFactors_nonempty_s53_oai : approximationFactors.Nonempty :=
  ⟨1 + 2 / Real.exp 1 + 1, factor_above_threshold_s53 1 zero_lt_one⟩

end MetricKMedian

end Inline_PCPInherited

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.approximationFactors_nonempty_s53_oai := @OAI.MetricKMedian.approximationFactors_nonempty_s53_oai
