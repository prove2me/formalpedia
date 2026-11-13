-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_64_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:41:50.577289+00:00
-- url     : https://prove2.me/submissions/2b913c4b-db65-4835-a864-ca9aa81000c5

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
theorem row_length_64_ca_oai : rowBuckets64.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_64_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_64_ca_oai
