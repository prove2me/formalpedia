-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_37_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:49:41.381221+00:00
-- url     : https://prove2.me/submissions/8cea505b-2e7b-4e70-9965-8c39d29207b5

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
theorem bucket_aug_37_ca_oai : ((residualBucket 37).map Prod.snd).sum = -68295290 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_37_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_37_ca_oai
