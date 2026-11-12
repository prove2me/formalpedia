-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_121_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:35:03.089285+00:00
-- url     : https://prove2.me/submissions/3c41a08f-0400-45cf-a5e8-0bfe4a6e61bc

import Mathlib
import Definitions.Def_OAIQ229C013

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_121_ca_oai : rowBuckets121.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_121_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_121_ca_oai
