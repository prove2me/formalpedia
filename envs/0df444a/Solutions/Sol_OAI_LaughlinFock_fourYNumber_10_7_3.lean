-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:30:32.225452+00:00
-- url     : https://prove2.me/submissions/02d14162-fd34-45fd-be40-fa161d922abb

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



theorem fourYNumber_10_7_3_oai :
    (collectedFourPartsTrace 10 7 3 collectedFourData_10 : ℚ) / fourCommonDenominator = (27875776847130353195239319289/214748364800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_7_3_oai := @OAI.LaughlinFock.fourYNumber_10_7_3_oai
