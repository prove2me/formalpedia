-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.periodExpC_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:38:56.611736+00:00
-- url     : https://prove2.me/submissions/77409bf6-09fc-485c-8945-0e064f1ea70a

import Mathlib
import Definitions.Def_OAIQ257X005

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma periodExpC_calc_x_oai (j : Fin 31) : (CI.ofReal ((envelopePhase10 j).re.mul (RI.point 36))).exp.re=periodExpC j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.periodExpC_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.periodExpC_calc_x_oai
