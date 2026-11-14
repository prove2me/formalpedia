-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_25_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:13:25.745331+00:00
-- url     : https://prove2.me/submissions/5a87fdfc-10cb-496f-a8c9-be8f563fdd8f

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
theorem bucket_l1_25_ca_oai : intL1 (residualBucket 25) = 244932860 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_25_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_25_ca_oai
