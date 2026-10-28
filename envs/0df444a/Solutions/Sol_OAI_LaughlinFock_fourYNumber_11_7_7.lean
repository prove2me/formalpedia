-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:41:30.887984+00:00
-- url     : https://prove2.me/submissions/a488f3cd-e8d9-447e-a9d2-a5f6be6cbfc5

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



theorem fourYNumber_11_7_7_oai :
    (collectedFourPartsTrace 11 7 7 collectedFourData_11 : ℚ) / fourCommonDenominator = (-237367962714551377912277743917/4294967296000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_7_7_oai := @OAI.LaughlinFock.fourYNumber_11_7_7_oai
