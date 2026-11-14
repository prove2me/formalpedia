-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_70_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:26:28.857669+00:00
-- url     : https://prove2.me/submissions/8bec8a03-de0f-4ab9-8d81-3c4ccbf2508c

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
theorem bucket_aug_70_ca_oai : ((residualBucket 70).map Prod.snd).sum = 31495500 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_70_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_70_ca_oai
