-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_16_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:39:30.710023+00:00
-- url     : https://prove2.me/submissions/8c3a12c6-9309-4a3e-9b81-adc999e5ea53

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
theorem row_length_16_ca_oai : rowBuckets16.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_16_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_16_ca_oai
