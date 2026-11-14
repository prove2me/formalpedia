-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_85_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:38:00.113887+00:00
-- url     : https://prove2.me/submissions/c6c8acb6-65b5-4a21-a845-e47cb25c3737

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
theorem bucket_aug_85_ca_oai : ((residualBucket 85).map Prod.snd).sum = 5641620 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_85_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_85_ca_oai
