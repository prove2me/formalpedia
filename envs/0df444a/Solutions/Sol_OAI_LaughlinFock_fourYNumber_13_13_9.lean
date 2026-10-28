-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:49:42.148136+00:00
-- url     : https://prove2.me/submissions/a8153a27-c467-4c24-a226-7f4a154b4b80

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_13_13_9_oai :
    (collectedFourPartsTrace 13 13 9 collectedFourData_13 : ℚ) / fourCommonDenominator = (-32349288923635241335157434197/26843545600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_13_9_oai := @OAI.LaughlinFock.fourYNumber_13_13_9_oai
