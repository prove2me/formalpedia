-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_11_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:34:09.621577+00:00
-- url     : https://prove2.me/submissions/680c2b3a-1094-41ff-afe4-4a21f0337e30

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



theorem fourYNumber_11_11_5_oai :
    (collectedFourPartsTrace 11 11 5 collectedFourData_11 : ℚ) / fourCommonDenominator = (7480163841350538966655866399/107374182400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_11_5_oai := @OAI.LaughlinFock.fourYNumber_11_11_5_oai
