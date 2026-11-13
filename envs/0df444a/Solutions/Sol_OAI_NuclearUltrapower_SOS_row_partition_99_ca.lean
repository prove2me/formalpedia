-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_99_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:25:08.91578+00:00
-- url     : https://prove2.me/submissions/f139a3a9-90d6-43a6-8392-96a0d1ed55a6

import Mathlib
import Definitions.Def_OAIQ229C023

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
theorem row_partition_99_ca_oai : normalize matLe residualRow99 = normalize matLe rowBuckets99.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_99_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_99_ca_oai
