-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_7_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:51:24.78532+00:00
-- url     : https://prove2.me/submissions/76967f6f-1623-4e1d-9bdf-6e4f5da994eb

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



theorem fourYNumber_7_7_7_oai :
    (shortNumericRowsFourTrace 7 7 7 : ℚ) / fourCommonDenominator = (-148920474389511901767358542711/34359738368000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_7_7_7_oai := @OAI.LaughlinFock.fourYNumber_7_7_7_oai
