-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_46_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:55:26.178256+00:00
-- url     : https://prove2.me/submissions/a2b910ae-c973-42a4-8372-ee621253c80e

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
theorem row_length_46_ca_oai : rowBuckets46.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_46_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_46_ca_oai
