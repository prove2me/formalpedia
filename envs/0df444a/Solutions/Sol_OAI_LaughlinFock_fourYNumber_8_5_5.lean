-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:04:22.386869+00:00
-- url     : https://prove2.me/submissions/8ec76ea5-6a2a-4906-a072-7b4a5b72e399

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



theorem fourYNumber_8_5_5_oai :
    (collectedFourPartsTrace 8 5 5 collectedFourData_8 : ℚ) / fourCommonDenominator = (-2472410179928723052502001181/1073741824000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_5_5_oai := @OAI.LaughlinFock.fourYNumber_8_5_5_oai
