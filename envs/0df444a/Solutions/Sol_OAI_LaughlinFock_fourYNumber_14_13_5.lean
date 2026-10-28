-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_13_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:54:54.280735+00:00
-- url     : https://prove2.me/submissions/2c15834c-5478-46da-b5c8-333726d64222

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



theorem fourYNumber_14_13_5_oai :
    (collectedFourPartsTrace 14 13 5 collectedFourData_14 : ℚ) / fourCommonDenominator = (-15546338707404656166201221607/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_13_5_oai := @OAI.LaughlinFock.fourYNumber_14_13_5_oai
