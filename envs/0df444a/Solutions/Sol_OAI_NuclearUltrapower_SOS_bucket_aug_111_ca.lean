-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_111_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:25:50.675833+00:00
-- url     : https://prove2.me/submissions/cfd265b2-daae-4bb1-8923-4027c3eecfae

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
theorem bucket_aug_111_ca_oai : ((residualBucket 111).map Prod.snd).sum = -180180340 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_111_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_111_ca_oai
