-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_122_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:31:18.067123+00:00
-- url     : https://prove2.me/submissions/2cd6c70c-9b5a-4a38-8904-31b1de7fa8f2

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
theorem bucket_aug_122_ca_oai : ((residualBucket 122).map Prod.snd).sum = -31904450 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_122_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_122_ca_oai
