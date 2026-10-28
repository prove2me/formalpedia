-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:50:50.847989+00:00
-- url     : https://prove2.me/submissions/79ba8943-7119-4cf7-9e6e-67b647fd1bc7

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



theorem fourYNumber_13_7_3_oai :
    (collectedFourPartsTrace 13 7 3 collectedFourData_13 : ℚ) / fourCommonDenominator = (-336594871328110409131740050319/107374182400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_7_3_oai := @OAI.LaughlinFock.fourYNumber_13_7_3_oai
