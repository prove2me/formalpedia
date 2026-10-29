-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:58:02.069002+00:00
-- url     : https://prove2.me/submissions/182adf66-786c-4703-8c3b-3e3b4fd197f3

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



theorem fourYNumber_15_7_1_oai :
    (collectedFourTrace 15 7 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (12612366434934957846304143447453/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_7_1_oai := @OAI.LaughlinFock.fourYNumber_15_7_1_oai
