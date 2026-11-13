-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_0_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:04:55.31619+00:00
-- url     : https://prove2.me/submissions/b0d7c4f5-e830-42f7-a52e-3f2129febade

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
theorem bucket_aug_0_ca_oai : ((residualBucket 0).map Prod.snd).sum = 114997080 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_0_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_0_ca_oai
