-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:03:34.376911+00:00
-- url     : https://prove2.me/submissions/34fe4d23-86c0-405e-b3c3-9fa0148d221c

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



theorem fourYNumber_8_1_1_oai :
    (collectedFourPartsTrace 8 1 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (-63725659480009131775992546879/536870912000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_1_1_oai := @OAI.LaughlinFock.fourYNumber_8_1_1_oai
