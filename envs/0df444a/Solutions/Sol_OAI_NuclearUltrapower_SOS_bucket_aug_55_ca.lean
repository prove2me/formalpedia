-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_55_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:01:11.053061+00:00
-- url     : https://prove2.me/submissions/5d36165a-c623-4b6b-ae55-919140a36346

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
theorem bucket_aug_55_ca_oai : ((residualBucket 55).map Prod.snd).sum = -22975480 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_55_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_55_ca_oai
