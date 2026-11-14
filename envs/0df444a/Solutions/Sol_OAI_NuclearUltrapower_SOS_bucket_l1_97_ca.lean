-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_97_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:47:43.889697+00:00
-- url     : https://prove2.me/submissions/0525a5c4-1839-4140-8e0b-ad5439f9326b

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
theorem bucket_l1_97_ca_oai : intL1 (residualBucket 97) = 255899150 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_97_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_97_ca_oai
