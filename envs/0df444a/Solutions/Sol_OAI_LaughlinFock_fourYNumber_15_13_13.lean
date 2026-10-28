-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:59:43.314837+00:00
-- url     : https://prove2.me/submissions/5b7c18f1-8b31-4b7e-a4ca-72a26b5e0c25

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



theorem fourYNumber_15_13_13_oai :
    (collectedFourTrace 15 13 13 collectedFourData_15 : ℚ) / fourCommonDenominator = (-171164208681192557791375250121/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_13_13_oai := @OAI.LaughlinFock.fourYNumber_15_13_13_oai
