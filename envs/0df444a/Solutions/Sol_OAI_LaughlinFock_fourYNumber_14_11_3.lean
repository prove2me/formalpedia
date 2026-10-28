-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_11_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:53:25.26427+00:00
-- url     : https://prove2.me/submissions/bb3c409f-84a5-4bd1-9af7-0c0b94fc6b79

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



theorem fourYNumber_14_11_3_oai :
    (collectedFourPartsTrace 14 11 3 collectedFourData_14 : ℚ) / fourCommonDenominator = (158234983123199496672321772983/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_11_3_oai := @OAI.LaughlinFock.fourYNumber_14_11_3_oai
