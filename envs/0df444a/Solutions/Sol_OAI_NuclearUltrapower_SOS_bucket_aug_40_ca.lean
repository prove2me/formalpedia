-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_40_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:03:31.395481+00:00
-- url     : https://prove2.me/submissions/7500d3b3-58a5-4561-8937-986f6b3b86bf

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
theorem bucket_aug_40_ca_oai : ((residualBucket 40).map Prod.snd).sum = -24001280 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_40_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_40_ca_oai
