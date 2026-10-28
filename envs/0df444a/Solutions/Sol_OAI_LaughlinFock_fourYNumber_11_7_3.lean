-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:40:46.613867+00:00
-- url     : https://prove2.me/submissions/8325f433-164e-416a-b890-0191ece80bd7

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_11_7_3_oai :
    (collectedFourPartsTrace 11 7 3 collectedFourData_11 : ℚ) / fourCommonDenominator = (152067258827467245508923213633/1073741824000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_7_3_oai := @OAI.LaughlinFock.fourYNumber_11_7_3_oai
