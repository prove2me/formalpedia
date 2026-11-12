-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_17_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:53:46.275192+00:00
-- url     : https://prove2.me/submissions/74f1c980-7268-41bf-844e-672708590858

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
theorem row_partition_17_ca_oai : normalize matLe residualRow17 = normalize matLe rowBuckets17.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_17_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_17_ca_oai
