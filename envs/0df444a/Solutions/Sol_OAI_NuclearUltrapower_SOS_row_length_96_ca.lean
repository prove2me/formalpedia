-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_96_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T10:17:11.145207+00:00
-- url     : https://prove2.me/submissions/f5087f92-6122-441f-843f-293b0710e27d

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
theorem row_length_96_ca_oai : rowBuckets96.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_96_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_96_ca_oai
