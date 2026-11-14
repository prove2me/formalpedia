-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_90_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:53:19.825954+00:00
-- url     : https://prove2.me/submissions/d9087f1e-026a-4336-80a8-fc234ea00439

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
theorem row_length_90_ca_oai : rowBuckets90.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_90_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_90_ca_oai
