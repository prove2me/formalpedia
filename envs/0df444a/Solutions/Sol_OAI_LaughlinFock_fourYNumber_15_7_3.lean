-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:58:02.994637+00:00
-- url     : https://prove2.me/submissions/58e08d7c-2d39-46d8-8dcd-e7bfe876534d

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_15_7_3_oai :
    (collectedFourTrace 15 7 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (773582640636166926582031618527/13421772800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_7_3_oai := @OAI.LaughlinFock.fourYNumber_15_7_3_oai
