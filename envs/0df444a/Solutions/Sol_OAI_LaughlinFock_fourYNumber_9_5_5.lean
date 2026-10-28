-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:12:47.202016+00:00
-- url     : https://prove2.me/submissions/b64322c7-7693-43b9-8e1f-34d90bbb833a

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_9_5_5_oai :
    (collectedFourPartsTrace 9 5 5 collectedFourData_9 : ℚ) / fourCommonDenominator = (-46478716744801148895226746231/7516192768000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_5_5_oai := @OAI.LaughlinFock.fourYNumber_9_5_5_oai
