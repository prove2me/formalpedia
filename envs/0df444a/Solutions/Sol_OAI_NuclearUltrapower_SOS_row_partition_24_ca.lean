-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_24_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:42:26.426477+00:00
-- url     : https://prove2.me/submissions/088fcf4b-8136-4f37-962a-821cb1f8e281

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
theorem row_partition_24_ca_oai : normalize matLe residualRow24 = normalize matLe rowBuckets24.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_24_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_24_ca_oai
