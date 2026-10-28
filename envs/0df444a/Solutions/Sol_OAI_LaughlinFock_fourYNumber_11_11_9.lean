-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_11_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:35:59.55928+00:00
-- url     : https://prove2.me/submissions/74a1b43e-00cd-48b0-bab6-b4b405073348

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



theorem fourYNumber_11_11_9_oai :
    (collectedFourPartsTrace 11 11 9 collectedFourData_11 : ℚ) / fourCommonDenominator = (-3621872144856940147989219393/107374182400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_11_9_oai := @OAI.LaughlinFock.fourYNumber_11_11_9_oai
