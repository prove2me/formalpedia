-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_9_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:51:56.448309+00:00
-- url     : https://prove2.me/submissions/e44aa839-d0f4-4ded-896a-aef855ddee13

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



theorem fourYNumber_13_9_1_oai :
    (collectedFourPartsTrace 13 9 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (-355081805318944629813716960967/13421772800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_9_1_oai := @OAI.LaughlinFock.fourYNumber_13_9_1_oai
