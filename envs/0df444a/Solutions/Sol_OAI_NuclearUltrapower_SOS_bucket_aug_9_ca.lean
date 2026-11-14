-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_9_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:41:39.649569+00:00
-- url     : https://prove2.me/submissions/40ce5329-559f-4520-952d-183f49630b5d

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
theorem bucket_aug_9_ca_oai : ((residualBucket 9).map Prod.snd).sum = -98439110 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_9_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_9_ca_oai
