-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:03:37.009265+00:00
-- url     : https://prove2.me/submissions/13ed7c47-63fc-4a50-a49a-6dc88a44f12b

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_8_3_3_oai :
    (collectedFourPartsTrace 8 3 3 collectedFourData_8 : ℚ) / fourCommonDenominator = (-20669734241111819247651968649/7516192768000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_3_3_oai := @OAI.LaughlinFock.fourYNumber_8_3_3_oai
