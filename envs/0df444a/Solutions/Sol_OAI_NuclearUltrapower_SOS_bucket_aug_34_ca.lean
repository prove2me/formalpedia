-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_34_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:01:57.346185+00:00
-- url     : https://prove2.me/submissions/da4a500b-8427-4580-9227-110bdc9db822

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
theorem bucket_aug_34_ca_oai : ((residualBucket 34).map Prod.snd).sum = -33912740 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_34_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_34_ca_oai
