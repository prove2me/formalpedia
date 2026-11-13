-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_114_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:54:22.994505+00:00
-- url     : https://prove2.me/submissions/9338fdd2-7141-4f70-a8c1-5705671e7a03

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
theorem row_partition_114_ca_oai : normalize matLe residualRow114 = normalize matLe rowBuckets114.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_114_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_114_ca_oai
