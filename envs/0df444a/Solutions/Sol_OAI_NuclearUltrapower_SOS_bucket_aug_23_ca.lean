-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_23_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:38:21.98356+00:00
-- url     : https://prove2.me/submissions/8e89d1c7-4ad9-455b-8de3-d3634aba7648

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
theorem bucket_aug_23_ca_oai : ((residualBucket 23).map Prod.snd).sum = -31465070 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_23_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_23_ca_oai
