-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.periodExpC_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:42:38.86819+00:00
-- url     : https://prove2.me/submissions/ba9757e3-6efb-4b02-9a00-475382e5e83d

import Mathlib
import Definitions.Def_OAIQ334E005

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma periodExpC_calc_eu_oai (j : Fin 31) : (CI.ofReal ((envelopePhase10 j).re.mul (RI.point 36))).exp.re=periodExpC j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.periodExpC_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.periodExpC_calc_eu_oai
