-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:08:23.909922+00:00
-- url     : https://prove2.me/submissions/dacbebaa-1dd9-4467-9142-46ffbd79d91a

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



theorem fourYNumber_9_1_1_oai :
    (collectedFourPartsTrace 9 1 1 collectedFourData_9 : ℚ) / fourCommonDenominator = (-146091607413928872790325971761/268435456000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_1_1_oai := @OAI.LaughlinFock.fourYNumber_9_1_1_oai
