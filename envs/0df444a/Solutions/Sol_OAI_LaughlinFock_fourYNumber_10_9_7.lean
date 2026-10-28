-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_9_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:33:39.395896+00:00
-- url     : https://prove2.me/submissions/d161e893-b548-424c-bd73-6bea7d464714

import Mathlib
import Definitions.Def_OAIQ084L002
import Definitions.Def_OAIQ084L009

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_10_9_7_oai :
    (collectedFourPartsTrace 10 9 7 collectedFourData_10 : ℚ) / fourCommonDenominator = (-4590411174217141231271545953/1073741824000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_9_7_oai := @OAI.LaughlinFock.fourYNumber_10_9_7_oai
