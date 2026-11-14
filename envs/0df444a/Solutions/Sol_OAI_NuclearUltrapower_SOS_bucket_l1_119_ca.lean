-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_119_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:57:41.920507+00:00
-- url     : https://prove2.me/submissions/264151c0-af8d-4b69-8f8e-852396e84e8d

import Mathlib
import Definitions.Def_OAIQ229C027

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
theorem bucket_l1_119_ca_oai : intL1 (residualBucket 119) = 327632750 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_119_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_119_ca_oai
