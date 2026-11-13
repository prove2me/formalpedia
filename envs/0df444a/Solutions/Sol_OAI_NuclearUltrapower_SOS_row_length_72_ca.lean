-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_72_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:22:15.661192+00:00
-- url     : https://prove2.me/submissions/0cd7819e-b855-49e2-a0a4-46c371ba95a7

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
theorem row_length_72_ca_oai : rowBuckets72.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_72_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_72_ca_oai
