-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:15:18.876341+00:00
-- url     : https://prove2.me/submissions/c8fe9965-5d92-4727-8a1d-3a1f21b14749

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



theorem fourYNumber_9_7_1_oai :
    (collectedFourPartsTrace 9 7 1 collectedFourData_9 : ℚ) / fourCommonDenominator = (30789416395436608069256092953/2147483648000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_7_1_oai := @OAI.LaughlinFock.fourYNumber_9_7_1_oai
