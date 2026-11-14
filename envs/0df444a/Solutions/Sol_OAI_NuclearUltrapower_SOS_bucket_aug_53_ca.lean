-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_53_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:26:06.208624+00:00
-- url     : https://prove2.me/submissions/ae9be9d5-4b75-44b9-a224-4694e1029162

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
theorem bucket_aug_53_ca_oai : ((residualBucket 53).map Prod.snd).sum = -76933860 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_53_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_53_ca_oai
