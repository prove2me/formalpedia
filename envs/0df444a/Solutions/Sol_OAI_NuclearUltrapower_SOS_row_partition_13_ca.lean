-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_13_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:30:40.637939+00:00
-- url     : https://prove2.me/submissions/b597e86f-0cd3-46ec-a5b9-ca67001fba64

import Mathlib
import Definitions.Def_OAIQ229C013
import Definitions.Def_OAIQ229C015

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
theorem row_partition_13_ca_oai : normalize matLe residualRow13 = normalize matLe rowBuckets13.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_13_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_13_ca_oai
