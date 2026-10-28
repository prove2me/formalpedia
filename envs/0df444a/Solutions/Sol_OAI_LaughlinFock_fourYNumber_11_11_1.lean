-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_11_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:31:57.283962+00:00
-- url     : https://prove2.me/submissions/8066d3c7-091a-47af-abb2-c38e802ef8d2

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



theorem fourYNumber_11_11_1_oai :
    (collectedFourPartsTrace 11 11 1 collectedFourData_11 : ℚ) / fourCommonDenominator = (9515299162481273462940221121/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_11_1_oai := @OAI.LaughlinFock.fourYNumber_11_11_1_oai
