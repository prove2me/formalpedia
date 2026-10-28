-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_9_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:18:17.132983+00:00
-- url     : https://prove2.me/submissions/41b89f19-05ba-4e44-9538-671fc17640fe

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



theorem fourYNumber_9_9_7_oai :
    (collectedFourPartsTrace 9 9 7 collectedFourData_9 : ℚ) / fourCommonDenominator = (-85051785275352886328867049021/4294967296000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_9_7_oai := @OAI.LaughlinFock.fourYNumber_9_9_7_oai
