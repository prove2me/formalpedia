-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpC31_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:42:35.087799+00:00
-- url     : https://prove2.me/submissions/3c052318-2f89-418f-b845-e903b2ef4420

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
lemma envelopeExpC31_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 31))).exp.re=envelopeExpC31 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpC31_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpC31_calc_eu_oai
