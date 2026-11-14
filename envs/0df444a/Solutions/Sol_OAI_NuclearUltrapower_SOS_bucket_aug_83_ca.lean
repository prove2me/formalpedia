-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_83_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:42.25939+00:00
-- url     : https://prove2.me/submissions/2bc5fd2e-eec3-4dad-a588-5303c0e37139

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
theorem bucket_aug_83_ca_oai : ((residualBucket 83).map Prod.snd).sum = 12434940 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_83_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_83_ca_oai
