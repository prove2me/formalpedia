-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_9_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:12:03.569198+00:00
-- url     : https://prove2.me/submissions/6d095692-184f-4cba-96f3-b3ae74859aef

import Mathlib
import Definitions.Def_OAIQ084L022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem _root_.solution :
    (collectedFourPartsTrace 9 9 9 collectedFourData_9 : ℚ) / fourCommonDenominator = (-99131997774302568689042771217/1073741824000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end
