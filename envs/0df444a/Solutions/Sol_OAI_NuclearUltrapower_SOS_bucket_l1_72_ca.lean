-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_72_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:03:19.388109+00:00
-- url     : https://prove2.me/submissions/c8b6c578-0217-47b8-b9ca-4877dc3dca9b

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
theorem bucket_l1_72_ca_oai : intL1 (residualBucket 72) = 142610950 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_72_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_72_ca_oai
