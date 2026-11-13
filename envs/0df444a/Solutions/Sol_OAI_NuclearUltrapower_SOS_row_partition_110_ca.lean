-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_110_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:23:22.19459+00:00
-- url     : https://prove2.me/submissions/ef11e414-4b59-4c95-8cee-00db67f4375c

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C020

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_partition_110_ca_oai : normalize matLe residualRow110 = normalize matLe rowBuckets110.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_110_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_110_ca_oai
