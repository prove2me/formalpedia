-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_9_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:32:10.309786+00:00
-- url     : https://prove2.me/submissions/f30d7bca-a4c1-4468-80cc-bf3d612346e8

import Mathlib
import Definitions.Def_OAIQ084L002
import Definitions.Def_OAIQ084L009

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_10_9_1_oai :
    (collectedFourPartsTrace 10 9 1 collectedFourData_10 : ℚ) / fourCommonDenominator = (74331768409382616339850430283/134217728000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_9_1_oai := @OAI.LaughlinFock.fourYNumber_10_9_1_oai
