-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_125_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:03:44.471809+00:00
-- url     : https://prove2.me/submissions/0dfe64ca-aca7-461b-b26a-b230c276e089

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
theorem bucket_l1_125_ca_oai : intL1 (residualBucket 125) = 250719850 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_125_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_125_ca_oai
