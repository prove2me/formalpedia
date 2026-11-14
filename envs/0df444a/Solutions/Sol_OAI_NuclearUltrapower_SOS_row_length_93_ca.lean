-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_93_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:58:19.076192+00:00
-- url     : https://prove2.me/submissions/18e52cd3-b478-4856-9d8b-056df6f6c886

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
theorem row_length_93_ca_oai : rowBuckets93.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_93_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_93_ca_oai
