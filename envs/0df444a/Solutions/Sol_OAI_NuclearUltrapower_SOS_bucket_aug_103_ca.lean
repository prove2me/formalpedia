-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_103_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:56:27.34226+00:00
-- url     : https://prove2.me/submissions/ec84a4c0-4c01-46c5-bb76-dd4833774b17

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
theorem bucket_aug_103_ca_oai : ((residualBucket 103).map Prod.snd).sum = -161485080 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_103_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_103_ca_oai
