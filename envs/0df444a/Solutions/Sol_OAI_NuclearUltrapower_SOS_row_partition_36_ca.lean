-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_36_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T15:48:53.79823+00:00
-- url     : https://prove2.me/submissions/8a7133c3-c28a-4733-bb4a-b0dfaf9ad7da

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
theorem row_partition_36_ca_oai : normalize matLe residualRow36 = normalize matLe rowBuckets36.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_36_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_36_ca_oai
