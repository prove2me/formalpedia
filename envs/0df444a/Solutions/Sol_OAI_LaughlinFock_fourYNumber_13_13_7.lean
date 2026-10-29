-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:56:07.260991+00:00
-- url     : https://prove2.me/submissions/068b9be3-4ee0-4102-a3b7-5483d29480c0

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



theorem fourYNumber_13_13_7_oai :
    (collectedFourPartsTrace 13 13 7 collectedFourData_13 : ℚ) / fourCommonDenominator = (-6961929908725446971605721289/21474836480000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_13_7_oai := @OAI.LaughlinFock.fourYNumber_13_13_7_oai
