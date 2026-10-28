-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:01:41.967987+00:00
-- url     : https://prove2.me/submissions/c0d1e999-74a7-4f93-ac57-60a245aa3354

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_15_15_11_oai :
    (collectedFourTrace 15 15 11 collectedFourData_15 : ℚ) / fourCommonDenominator = (-39622599808406172905598670419/1073741824000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_15_11_oai := @OAI.LaughlinFock.fourYNumber_15_15_11_oai
