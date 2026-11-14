-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_17_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:32:05.424743+00:00
-- url     : https://prove2.me/submissions/48a6073d-e374-4484-84eb-19ddf07ca10d

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
theorem bucket_aug_17_ca_oai : ((residualBucket 17).map Prod.snd).sum = 57357320 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_17_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_17_ca_oai
