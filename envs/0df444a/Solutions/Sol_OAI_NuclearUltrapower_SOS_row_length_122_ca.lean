-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_122_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:46:08.661442+00:00
-- url     : https://prove2.me/submissions/d1233554-17f2-475b-a61e-fc0af3a16d42

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
theorem row_length_122_ca_oai : rowBuckets122.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_122_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_122_ca_oai
