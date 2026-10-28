-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_13_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:54:30.593217+00:00
-- url     : https://prove2.me/submissions/a61eb3b6-2928-43e4-b286-42b075cf6ac2

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



theorem fourYNumber_14_13_13_oai :
    (collectedFourPartsTrace 14 13 13 collectedFourData_14 : ℚ) / fourCommonDenominator = (-109065237409747857476663108541/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_13_13_oai := @OAI.LaughlinFock.fourYNumber_14_13_13_oai
