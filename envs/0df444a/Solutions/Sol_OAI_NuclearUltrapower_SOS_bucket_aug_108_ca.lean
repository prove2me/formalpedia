-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_108_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:59:23.161227+00:00
-- url     : https://prove2.me/submissions/6ea3a2b5-d706-4c29-910f-8b63cd06fcc6

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
theorem bucket_aug_108_ca_oai : ((residualBucket 108).map Prod.snd).sum = -19631680 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_108_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_108_ca_oai
