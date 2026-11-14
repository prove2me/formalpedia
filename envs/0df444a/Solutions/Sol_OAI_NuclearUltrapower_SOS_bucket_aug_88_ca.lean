-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_88_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:00:43.964247+00:00
-- url     : https://prove2.me/submissions/206144c2-d53d-427e-9d06-87aa41920613

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
theorem bucket_aug_88_ca_oai : ((residualBucket 88).map Prod.snd).sum = 229416240 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_88_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_88_ca_oai
