-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:36:45.051989+00:00
-- url     : https://prove2.me/submissions/4e8feffd-7ecf-4bca-96eb-07ca149b553b

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



theorem fourYNumber_11_3_3_oai :
    (collectedFourPartsTrace 11 3 3 collectedFourData_11 : ℚ) / fourCommonDenominator = (147990015194717604324970401939/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_3_3_oai := @OAI.LaughlinFock.fourYNumber_11_3_3_oai
