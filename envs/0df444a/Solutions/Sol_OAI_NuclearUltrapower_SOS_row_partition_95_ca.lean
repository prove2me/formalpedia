-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_95_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:19:35.897329+00:00
-- url     : https://prove2.me/submissions/677c22c2-b43b-4f58-9087-cbb4c98ad627

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
theorem row_partition_95_ca_oai : normalize matLe residualRow95 = normalize matLe rowBuckets95.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_95_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_95_ca_oai
