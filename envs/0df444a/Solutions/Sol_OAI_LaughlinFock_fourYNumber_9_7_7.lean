-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:16:26.699454+00:00
-- url     : https://prove2.me/submissions/ac410aa5-90cb-4d83-9e03-27256cf7a52e

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



theorem fourYNumber_9_7_7_oai :
    (collectedFourPartsTrace 9 7 7 collectedFourData_9 : ℚ) / fourCommonDenominator = (-105495675446941487863399344237/17179869184000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_7_7_oai := @OAI.LaughlinFock.fourYNumber_9_7_7_oai
