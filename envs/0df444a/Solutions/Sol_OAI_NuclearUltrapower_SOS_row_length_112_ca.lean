-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_112_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T12:12:22.875576+00:00
-- url     : https://prove2.me/submissions/9b22c9c5-72d8-4c00-8557-55af10d67c57

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
theorem row_length_112_ca_oai : rowBuckets112.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_112_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_112_ca_oai
