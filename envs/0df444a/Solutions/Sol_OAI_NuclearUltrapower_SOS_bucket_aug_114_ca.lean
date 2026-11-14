-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_114_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:57:14.339186+00:00
-- url     : https://prove2.me/submissions/23b2cca5-7bd3-49f6-86fc-5cb925b5e62f

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
theorem bucket_aug_114_ca_oai : ((residualBucket 114).map Prod.snd).sum = 43677320 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_114_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_114_ca_oai
