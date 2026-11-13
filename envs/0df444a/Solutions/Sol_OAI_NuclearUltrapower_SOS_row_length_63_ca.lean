-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_63_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:33:26.866185+00:00
-- url     : https://prove2.me/submissions/a27c9e35-1719-4879-833b-672aa843ee67

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
theorem row_length_63_ca_oai : rowBuckets63.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_63_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_63_ca_oai
