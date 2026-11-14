-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_124_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:30:33.487203+00:00
-- url     : https://prove2.me/submissions/3f5d1616-992c-450f-8ba8-5c00e770a4cc

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
theorem bucket_aug_124_ca_oai : ((residualBucket 124).map Prod.snd).sum = 172112740 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_124_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_124_ca_oai
