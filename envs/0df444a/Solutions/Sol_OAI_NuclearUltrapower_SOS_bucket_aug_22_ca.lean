-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_22_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:00:44.916429+00:00
-- url     : https://prove2.me/submissions/4296b7f3-3245-435f-8b16-122ba4790dd3

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
theorem bucket_aug_22_ca_oai : ((residualBucket 22).map Prod.snd).sum = 61877360 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_22_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_22_ca_oai
