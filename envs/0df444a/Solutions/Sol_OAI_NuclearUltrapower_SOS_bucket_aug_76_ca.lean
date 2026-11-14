-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_76_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:09:47.147361+00:00
-- url     : https://prove2.me/submissions/7e0e1a17-7085-4134-93d5-f44ce01f9fd2

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
theorem bucket_aug_76_ca_oai : ((residualBucket 76).map Prod.snd).sum = 166299570 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_76_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_76_ca_oai
