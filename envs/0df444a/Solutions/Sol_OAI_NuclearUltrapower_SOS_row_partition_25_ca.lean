-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_25_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:42:03.088822+00:00
-- url     : https://prove2.me/submissions/b1cb4365-120c-4da2-a69e-23e9e64d0468

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
theorem row_partition_25_ca_oai : normalize matLe residualRow25 = normalize matLe rowBuckets25.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_25_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_25_ca_oai
