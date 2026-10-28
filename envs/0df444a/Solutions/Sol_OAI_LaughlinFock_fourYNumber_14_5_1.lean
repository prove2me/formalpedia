-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:57:07.539596+00:00
-- url     : https://prove2.me/submissions/f8635a07-f7ca-4653-9d16-9a20b1412052

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_14_5_1_oai :
    (collectedFourPartsTrace 14 5 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (4218556651632078178090845049587/1677721600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_5_1_oai := @OAI.LaughlinFock.fourYNumber_14_5_1_oai
