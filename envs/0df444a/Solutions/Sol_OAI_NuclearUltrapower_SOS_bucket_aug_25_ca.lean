-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_25_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:02:21.158541+00:00
-- url     : https://prove2.me/submissions/1b5609e3-144d-484e-ae94-a8385f41afcd

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
theorem bucket_aug_25_ca_oai : ((residualBucket 25).map Prod.snd).sum = -4838740 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_25_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_25_ca_oai
