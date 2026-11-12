-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_14_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T00:42:17.368224+00:00
-- url     : https://prove2.me/submissions/ed0c2066-85fc-492a-a48f-589bdec3e123

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
theorem row_length_14_ca_oai : rowBuckets14.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_14_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_14_ca_oai
