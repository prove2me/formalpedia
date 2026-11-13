-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_101_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T02:29:30.848668+00:00
-- url     : https://prove2.me/submissions/ae58fd44-009a-4aa3-afc0-01a242f5b229

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
theorem bucket_aug_101_ca_oai : ((residualBucket 101).map Prod.snd).sum = -104584660 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_101_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_101_ca_oai
