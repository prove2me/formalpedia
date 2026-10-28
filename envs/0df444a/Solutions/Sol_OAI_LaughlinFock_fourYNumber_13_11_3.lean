-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_11_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:45:14.954888+00:00
-- url     : https://prove2.me/submissions/e9e9e6bf-26ff-4c8d-ac00-aee6df3ab4af

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



theorem fourYNumber_13_11_3_oai :
    (collectedFourPartsTrace 13 11 3 collectedFourData_13 : ℚ) / fourCommonDenominator = (-53741237690979222629963864157/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_11_3_oai := @OAI.LaughlinFock.fourYNumber_13_11_3_oai
