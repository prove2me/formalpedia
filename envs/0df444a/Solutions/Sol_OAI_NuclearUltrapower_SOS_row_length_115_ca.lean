-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_115_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T00:16:41.604206+00:00
-- url     : https://prove2.me/submissions/0f3808a7-8ab5-4031-9207-e1af184eb988

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
theorem row_length_115_ca_oai : rowBuckets115.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_115_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_115_ca_oai
