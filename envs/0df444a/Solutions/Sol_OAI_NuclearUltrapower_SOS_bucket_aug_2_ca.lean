-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_2_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:05:55.640963+00:00
-- url     : https://prove2.me/submissions/290b6c51-3595-44cf-a96b-2efa87e155a8

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
theorem bucket_aug_2_ca_oai : ((residualBucket 2).map Prod.snd).sum = -7961320 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_2_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_2_ca_oai
