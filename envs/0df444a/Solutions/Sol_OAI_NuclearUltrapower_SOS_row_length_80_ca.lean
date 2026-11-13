-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_80_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:14:01.545079+00:00
-- url     : https://prove2.me/submissions/31125631-5cab-490b-872e-7cd67438e8fb

import Mathlib
import Definitions.Def_OAIQ229C022

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_80_ca_oai : rowBuckets80.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_80_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_80_ca_oai
