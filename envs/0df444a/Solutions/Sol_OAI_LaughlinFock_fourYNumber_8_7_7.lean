-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:08:23.012926+00:00
-- url     : https://prove2.me/submissions/f575d686-721f-4a9e-9274-314e56aa9303

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



theorem fourYNumber_8_7_7_oai :
    (collectedFourPartsTrace 8 7 7 collectedFourData_8 : ℚ) / fourCommonDenominator = (-178020445962132587387054522433/17179869184000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_7_7_oai := @OAI.LaughlinFock.fourYNumber_8_7_7_oai
