-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:47:49.752054+00:00
-- url     : https://prove2.me/submissions/39f975fd-f7aa-48e0-9c52-c51a614fe1f5

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



theorem fourYNumber_13_13_1_oai :
    (collectedFourPartsTrace 13 13 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (-10573066740063296657251598628951/13421772800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_13_1_oai := @OAI.LaughlinFock.fourYNumber_13_13_1_oai
