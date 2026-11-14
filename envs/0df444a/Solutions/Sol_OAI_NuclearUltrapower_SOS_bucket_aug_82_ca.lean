-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_82_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:27:57.905059+00:00
-- url     : https://prove2.me/submissions/a8a8fb16-0886-49ef-9209-a971c839afcd

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
theorem bucket_aug_82_ca_oai : ((residualBucket 82).map Prod.snd).sum = -84701560 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_82_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_82_ca_oai
