-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:31:00.238749+00:00
-- url     : https://prove2.me/submissions/7d10f754-f56b-4882-b2a4-4eece55b2589

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



theorem fourYNumber_10_7_7_oai :
    (collectedFourPartsTrace 10 7 7 collectedFourData_10 : ℚ) / fourCommonDenominator = (88212964072712605466404249449/4294967296000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_7_7_oai := @OAI.LaughlinFock.fourYNumber_10_7_7_oai
