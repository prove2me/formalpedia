-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_121_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:45:27.013871+00:00
-- url     : https://prove2.me/submissions/2fcc4c7a-5be9-4184-973e-41244b14f430

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
theorem row_partition_121_ca_oai : normalize matLe residualRow121 = normalize matLe rowBuckets121.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_121_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_121_ca_oai
