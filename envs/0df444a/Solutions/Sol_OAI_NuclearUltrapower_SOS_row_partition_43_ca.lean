-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_43_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:00:53.51157+00:00
-- url     : https://prove2.me/submissions/c47455f8-dfa6-4cd4-9aaf-9d2f3055710a

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
theorem row_partition_43_ca_oai : normalize matLe residualRow43 = normalize matLe rowBuckets43.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_43_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_43_ca_oai
