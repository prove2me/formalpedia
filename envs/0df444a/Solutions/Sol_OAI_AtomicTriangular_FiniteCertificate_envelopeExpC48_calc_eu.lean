-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpC48_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:43:40.742557+00:00
-- url     : https://prove2.me/submissions/57c17bcb-7a3a-40a6-9e0c-fcc7089937d7

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
lemma envelopeExpC48_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 48))).exp.re=envelopeExpC48 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpC48_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpC48_calc_eu_oai
