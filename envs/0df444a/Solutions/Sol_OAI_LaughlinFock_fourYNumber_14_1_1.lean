-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:56:00.923992+00:00
-- url     : https://prove2.me/submissions/892f85ae-57f7-45cb-b755-27cc209bc248

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



theorem fourYNumber_14_1_1_oai :
    (collectedFourPartsTrace 14 1 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (-73743456216689631429868109022867/1677721600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_1_1_oai := @OAI.LaughlinFock.fourYNumber_14_1_1_oai
