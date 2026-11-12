-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_18_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:55:58.870206+00:00
-- url     : https://prove2.me/submissions/c0d9d637-02bd-4fe0-84e8-cd8ffd9664c9

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
theorem row_partition_18_ca_oai : normalize matLe residualRow18 = normalize matLe rowBuckets18.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_18_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_18_ca_oai
