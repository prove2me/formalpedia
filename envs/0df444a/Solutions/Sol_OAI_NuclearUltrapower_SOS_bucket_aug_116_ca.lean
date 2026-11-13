-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_116_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:11:07.341195+00:00
-- url     : https://prove2.me/submissions/a46c1b37-d0a6-4757-a92f-4183465f6b3b

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
theorem bucket_aug_116_ca_oai : ((residualBucket 116).map Prod.snd).sum = -48734770 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_116_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_116_ca_oai
