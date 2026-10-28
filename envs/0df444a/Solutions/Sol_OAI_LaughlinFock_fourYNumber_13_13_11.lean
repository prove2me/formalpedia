-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:47:50.728393+00:00
-- url     : https://prove2.me/submissions/a5e5ae95-d97d-4213-830a-ca5090401129

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



theorem fourYNumber_13_13_11_oai :
    (collectedFourPartsTrace 13 13 11 collectedFourData_13 : ℚ) / fourCommonDenominator = (111617540419977191224126903401/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_13_11_oai := @OAI.LaughlinFock.fourYNumber_13_13_11_oai
