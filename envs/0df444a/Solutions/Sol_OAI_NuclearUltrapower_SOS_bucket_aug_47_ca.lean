-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_47_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:58:24.786321+00:00
-- url     : https://prove2.me/submissions/f5587b1e-a704-49ee-8330-3f270d8b759d

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
theorem bucket_aug_47_ca_oai : ((residualBucket 47).map Prod.snd).sum = 28955020 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_47_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_47_ca_oai
