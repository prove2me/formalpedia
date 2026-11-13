-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_78_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:08:46.368982+00:00
-- url     : https://prove2.me/submissions/1471f77d-d9fe-45d9-b72f-9bf7f8e02048

import Mathlib
import Definitions.Def_OAIQ229C022

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_78_ca_oai : rowBuckets78.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_78_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_78_ca_oai
