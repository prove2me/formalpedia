-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_92_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:30:32.536197+00:00
-- url     : https://prove2.me/submissions/11869f8a-3b35-4ac5-8d44-0e639a49fa93

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
theorem bucket_aug_92_ca_oai : ((residualBucket 92).map Prod.snd).sum = -48297600 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_92_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_92_ca_oai
