-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_11_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:53:02.903287+00:00
-- url     : https://prove2.me/submissions/4b6c754a-c469-42df-9c8a-d0fa8219bbca

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



theorem fourYNumber_14_11_11_oai :
    (collectedFourPartsTrace 14 11 11 collectedFourData_14 : ℚ) / fourCommonDenominator = (19121697292235405186772511839/13421772800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_11_11_oai := @OAI.LaughlinFock.fourYNumber_14_11_11_oai
