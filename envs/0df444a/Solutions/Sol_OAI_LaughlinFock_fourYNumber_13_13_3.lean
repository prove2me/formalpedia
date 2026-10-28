-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:48:36.288008+00:00
-- url     : https://prove2.me/submissions/63f3d1c4-411c-48c1-8e22-a594c73eec5e

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_13_13_3_oai :
    (collectedFourPartsTrace 13 13 3 collectedFourData_13 : ℚ) / fourCommonDenominator = (-322958874522253767236148992139/26843545600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_13_3_oai := @OAI.LaughlinFock.fourYNumber_13_13_3_oai
