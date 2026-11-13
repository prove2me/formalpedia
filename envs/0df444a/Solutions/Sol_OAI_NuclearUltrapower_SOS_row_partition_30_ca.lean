-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_30_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:22:41.880192+00:00
-- url     : https://prove2.me/submissions/f0ce961a-357b-4639-93d2-afc4f4fef16e

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
theorem row_partition_30_ca_oai : normalize matLe residualRow30 = normalize matLe rowBuckets30.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_30_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_30_ca_oai
