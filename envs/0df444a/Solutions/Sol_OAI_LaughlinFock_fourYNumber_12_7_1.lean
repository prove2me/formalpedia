-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_12_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:38:42.32701+00:00
-- url     : https://prove2.me/submissions/6f8e863f-8989-4bc5-b3fd-8e0c113bc81f

import Mathlib
import Definitions.Def_OAIQ084L015

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate12Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_12_7_1_oai :
    (shortNumericRowsFourTrace 12 7 1 : ℚ) / fourCommonDenominator = (-752813653217822024111461724931/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_12_7_1_oai := @OAI.LaughlinFock.fourYNumber_12_7_1_oai
