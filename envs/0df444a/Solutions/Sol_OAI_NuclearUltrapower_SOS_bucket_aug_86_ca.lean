-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_86_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:30:55.540109+00:00
-- url     : https://prove2.me/submissions/463bdafb-0012-4ff0-a048-90b7f44842dd

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
theorem bucket_aug_86_ca_oai : ((residualBucket 86).map Prod.snd).sum = -44903750 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_86_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_86_ca_oai
