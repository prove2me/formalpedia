-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_104_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:33:57.204874+00:00
-- url     : https://prove2.me/submissions/9c78a59d-dd0f-4c15-a7b8-84183df8cc51

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
theorem bucket_aug_104_ca_oai : ((residualBucket 104).map Prod.snd).sum = 116391670 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_104_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_104_ca_oai
