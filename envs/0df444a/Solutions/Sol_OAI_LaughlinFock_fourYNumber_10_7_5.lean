-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_7_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:30:33.20793+00:00
-- url     : https://prove2.me/submissions/7ba30354-1e78-4c57-be81-456cd5a90398

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



theorem fourYNumber_10_7_5_oai :
    (collectedFourPartsTrace 10 7 5 collectedFourData_10 : ℚ) / fourCommonDenominator = (-8781593118050446480941197751/214748364800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_7_5_oai := @OAI.LaughlinFock.fourYNumber_10_7_5_oai
