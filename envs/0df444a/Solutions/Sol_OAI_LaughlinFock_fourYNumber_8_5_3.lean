-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:03:59.601824+00:00
-- url     : https://prove2.me/submissions/6e9927b7-3368-421c-8883-cf7c34399001

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_8_5_3_oai :
    (collectedFourPartsTrace 8 5 3 collectedFourData_8 : ℚ) / fourCommonDenominator = (9455940384238314087831042759/3758096384000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_5_3_oai := @OAI.LaughlinFock.fourYNumber_8_5_3_oai
