-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_41_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:33.376327+00:00
-- url     : https://prove2.me/submissions/c4fbff98-7d87-4735-a6f2-2e0f79394e7c

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
theorem bucket_aug_41_ca_oai : ((residualBucket 41).map Prod.snd).sum = 63218990 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_41_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_41_ca_oai
