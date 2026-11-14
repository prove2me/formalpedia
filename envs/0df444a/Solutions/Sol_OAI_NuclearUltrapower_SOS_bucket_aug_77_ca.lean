-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_77_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:10:11.112661+00:00
-- url     : https://prove2.me/submissions/890e98f2-65ca-44a3-bb68-254672058e2c

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
theorem bucket_aug_77_ca_oai : ((residualBucket 77).map Prod.snd).sum = 84184570 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_77_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_77_ca_oai
