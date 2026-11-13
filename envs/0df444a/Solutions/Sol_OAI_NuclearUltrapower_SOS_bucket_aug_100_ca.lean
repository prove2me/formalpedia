-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_100_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T00:47:35.065202+00:00
-- url     : https://prove2.me/submissions/db5f99b7-b176-4a4b-99f8-141823c63e58

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
theorem bucket_aug_100_ca_oai : ((residualBucket 100).map Prod.snd).sum = -14017540 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_100_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_100_ca_oai
