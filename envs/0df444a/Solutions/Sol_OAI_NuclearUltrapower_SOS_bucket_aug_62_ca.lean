-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_62_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:15:46.835998+00:00
-- url     : https://prove2.me/submissions/8c7f3ae1-066a-4177-8757-1f6475636bf9

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
theorem bucket_aug_62_ca_oai : ((residualBucket 62).map Prod.snd).sum = -26369630 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_62_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_62_ca_oai
