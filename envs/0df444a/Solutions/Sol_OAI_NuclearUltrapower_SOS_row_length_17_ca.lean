-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_17_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:53:00.859195+00:00
-- url     : https://prove2.me/submissions/a44bf79c-f12c-411d-a844-74f34d5b049b

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
theorem row_length_17_ca_oai : rowBuckets17.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_17_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_17_ca_oai
