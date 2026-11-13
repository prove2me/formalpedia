-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_123_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:50:58.661365+00:00
-- url     : https://prove2.me/submissions/f35d4785-2641-44b3-991d-e8777324f5c4

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
theorem bucket_aug_123_ca_oai : ((residualBucket 123).map Prod.snd).sum = -9992680 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_123_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_123_ca_oai
