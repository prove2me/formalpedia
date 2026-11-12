-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_40_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:48:29.15538+00:00
-- url     : https://prove2.me/submissions/e844ffe5-301e-4b30-91f3-3027772cf485

import Mathlib
import Definitions.Def_OAIQ229C021

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_40_ca_oai : rowBuckets40.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_40_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_40_ca_oai
