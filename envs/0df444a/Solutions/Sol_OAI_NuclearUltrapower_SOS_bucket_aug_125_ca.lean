-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_125_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:35:49.716517+00:00
-- url     : https://prove2.me/submissions/b028c1ed-7f50-47bd-98b8-30bc4fd6d7e6

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
theorem bucket_aug_125_ca_oai : ((residualBucket 125).map Prod.snd).sum = 47149430 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_125_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_125_ca_oai
