-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_117_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:09:24.534097+00:00
-- url     : https://prove2.me/submissions/7920b921-19dc-44a3-b076-6d89f7f34f48

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
theorem bucket_aug_117_ca_oai : ((residualBucket 117).map Prod.snd).sum = -18528820 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_117_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_117_ca_oai
