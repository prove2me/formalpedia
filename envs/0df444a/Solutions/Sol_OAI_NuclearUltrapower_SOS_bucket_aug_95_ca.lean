-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_95_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:32:52.12223+00:00
-- url     : https://prove2.me/submissions/210503d0-ec74-4a0e-968e-ae606862536d

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
theorem bucket_aug_95_ca_oai : ((residualBucket 95).map Prod.snd).sum = 43022550 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_95_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_95_ca_oai
