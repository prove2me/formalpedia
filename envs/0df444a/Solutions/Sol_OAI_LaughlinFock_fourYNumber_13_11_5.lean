-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_11_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:45:59.103026+00:00
-- url     : https://prove2.me/submissions/ce73c0b2-c672-4215-ba16-eee217d0e4bf

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



theorem fourYNumber_13_11_5_oai :
    (collectedFourPartsTrace 13 11 5 collectedFourData_13 : ℚ) / fourCommonDenominator = (-68930057095502634567023048451/26843545600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_11_5_oai := @OAI.LaughlinFock.fourYNumber_13_11_5_oai
