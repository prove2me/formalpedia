-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_10_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T02:07:28.643889+00:00
-- url     : https://prove2.me/submissions/b6508995-0218-4546-9238-90c8c39a9522

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
theorem bucket_aug_10_ca_oai : ((residualBucket 10).map Prod.snd).sum = -110131670 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_10_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_10_ca_oai
