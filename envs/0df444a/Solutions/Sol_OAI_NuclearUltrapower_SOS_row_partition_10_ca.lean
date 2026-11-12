-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_10_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:08:05.243385+00:00
-- url     : https://prove2.me/submissions/5b185932-b276-4478-8e2c-9c0177258ed6

import Mathlib
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
theorem row_partition_10_ca_oai : normalize matLe residualRow10 = normalize matLe rowBuckets10.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_10_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_10_ca_oai
