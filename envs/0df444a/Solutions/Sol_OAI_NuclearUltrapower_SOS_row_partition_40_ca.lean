-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_40_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:31:42.77608+00:00
-- url     : https://prove2.me/submissions/6e09788d-db58-4d8b-929e-1a8b76f68238

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C021

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
theorem row_partition_40_ca_oai : normalize matLe residualRow40 = normalize matLe rowBuckets40.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_40_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_40_ca_oai
