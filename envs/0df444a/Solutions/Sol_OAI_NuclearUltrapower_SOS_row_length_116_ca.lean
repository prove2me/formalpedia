-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_116_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:33:24.694091+00:00
-- url     : https://prove2.me/submissions/ee11b1ed-e329-4be9-84bf-3cec32194211

import Mathlib
import Definitions.Def_OAIQ229C020

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_116_ca_oai : rowBuckets116.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_116_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_116_ca_oai
