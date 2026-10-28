-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_11_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:45:13.678108+00:00
-- url     : https://prove2.me/submissions/94b4b3d4-29f0-4e80-a50b-c4a76ebb130a

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



theorem fourYNumber_13_11_11_oai :
    (collectedFourPartsTrace 13 11 11 collectedFourData_13 : ℚ) / fourCommonDenominator = (-57551507789343683809289940729/21474836480000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_11_11_oai := @OAI.LaughlinFock.fourYNumber_13_11_11_oai
