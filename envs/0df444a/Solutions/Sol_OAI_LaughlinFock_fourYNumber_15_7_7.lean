-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:58:05.97406+00:00
-- url     : https://prove2.me/submissions/7c7a3e6d-dc7d-4067-8e60-3cb5a1a3730a

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



theorem fourYNumber_15_7_7_oai :
    (collectedFourTrace 15 7 7 collectedFourData_15 : ℚ) / fourCommonDenominator = (-571499890221638338551002497491/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_7_7_oai := @OAI.LaughlinFock.fourYNumber_15_7_7_oai
