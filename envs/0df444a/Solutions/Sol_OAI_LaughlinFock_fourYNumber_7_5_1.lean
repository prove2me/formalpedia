-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_7_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:48:47.070264+00:00
-- url     : https://prove2.me/submissions/a7aaef27-a720-4cb2-9d84-f395db98ca7e

import Mathlib
import Definitions.Def_OAIQ084L015

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_7_5_1_oai :
    (shortNumericRowsFourTrace 7 5 1 : ℚ) / fourCommonDenominator = (-106335364725988709134966359/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_7_5_1_oai := @OAI.LaughlinFock.fourYNumber_7_5_1_oai
