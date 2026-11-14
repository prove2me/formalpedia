-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_43_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:56:05.619082+00:00
-- url     : https://prove2.me/submissions/baf73038-fc26-4b5a-a88b-4e8b53e2dfb6

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
theorem bucket_aug_43_ca_oai : ((residualBucket 43).map Prod.snd).sum = 66722910 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_43_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_43_ca_oai
