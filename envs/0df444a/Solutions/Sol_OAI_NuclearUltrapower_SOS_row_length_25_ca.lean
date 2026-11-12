-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_25_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:18:07.002301+00:00
-- url     : https://prove2.me/submissions/2b235a4b-0fce-47cd-b55c-5775fd5614fd

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
theorem row_length_25_ca_oai : rowBuckets25.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_25_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_25_ca_oai
