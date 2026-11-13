-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpC37_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:24.794215+00:00
-- url     : https://prove2.me/submissions/d95ca361-9cdf-4394-9836-285a5e6e8ec4

import Mathlib
import Definitions.Def_OAIQ334E005

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpC37_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 37))).exp.re=envelopeExpC37 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpC37_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpC37_calc_eu_oai
