-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_95_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:47:34.013201+00:00
-- url     : https://prove2.me/submissions/63729a82-af23-463b-a2e4-60dcfcee9b49

import Mathlib
import Definitions.Def_OAIQ229C023

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
theorem row_length_95_ca_oai : rowBuckets95.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_95_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_95_ca_oai
