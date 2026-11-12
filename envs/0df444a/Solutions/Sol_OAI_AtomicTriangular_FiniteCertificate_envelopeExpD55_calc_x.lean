-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD55_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:38:00.174+00:00
-- url     : https://prove2.me/submissions/d419fe96-85a2-407b-ac77-dbf346f337f1

import Mathlib
import Definitions.Def_OAIQ257X004

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpD55_calc_x_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 55))).exp.re=envelopeExpD55 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD55_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD55_calc_x_oai
