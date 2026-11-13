-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_99_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:34:42.558844+00:00
-- url     : https://prove2.me/submissions/f04ef043-436d-4e37-9b38-82371b823fb3

import Mathlib
import Definitions.Def_OAIQ229C023

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
theorem row_length_99_ca_oai : rowBuckets99.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_99_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_99_ca_oai
