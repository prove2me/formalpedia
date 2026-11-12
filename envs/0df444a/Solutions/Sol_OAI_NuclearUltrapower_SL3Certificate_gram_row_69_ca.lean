-- Prove2me | solution 1 for OAI.NuclearUltrapower.SL3Certificate.gram_row_69_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:06:02.052579+00:00
-- url     : https://prove2.me/submissions/05c2f139-5bc9-48f0-9073-691e3a5343e2

import Mathlib
import Definitions.Def_OAIQ229C004
import Definitions.Def_OAIQ229C006

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
theorem gram_row_69_ca_oai : columns.map (dot q69) = g69 := by decide +kernel
end NuclearUltrapower.SL3Certificate
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SL3Certificate.gram_row_69_ca_oai := @OAI.NuclearUltrapower.SL3Certificate.gram_row_69_ca_oai
