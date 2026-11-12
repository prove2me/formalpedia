-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_15_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T00:22:13.770331+00:00
-- url     : https://prove2.me/submissions/a50ee6dc-5de8-43e9-94f3-11ceb65fede4

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
theorem row_length_15_ca_oai : rowBuckets15.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_15_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_15_ca_oai
