-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_12_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:45:07.721742+00:00
-- url     : https://prove2.me/submissions/09330ddd-3edd-4b08-ac87-df14a508149a

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



theorem fourYNumber_12_3_1_oai :
    (shortNumericRowsFourTrace 12 3 1 : ℚ) / fourCommonDenominator = (895702254134345728636174721541/13421772800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_12_3_1_oai := @OAI.LaughlinFock.fourYNumber_12_3_1_oai
