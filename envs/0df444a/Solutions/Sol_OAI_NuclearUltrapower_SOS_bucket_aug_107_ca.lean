-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_107_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:01:56.343746+00:00
-- url     : https://prove2.me/submissions/6ba7d5f8-6172-4a45-9658-f37cb3280936

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
theorem bucket_aug_107_ca_oai : ((residualBucket 107).map Prod.snd).sum = -34954090 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_107_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_107_ca_oai
