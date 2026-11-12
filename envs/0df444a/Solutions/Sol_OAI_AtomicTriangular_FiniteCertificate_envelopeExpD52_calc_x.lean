-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD52_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:37:34.535997+00:00
-- url     : https://prove2.me/submissions/8b30e391-07ee-497b-b2fe-83a8d2f7f23a

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
lemma envelopeExpD52_calc_x_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 52))).exp.re=envelopeExpD52 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD52_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD52_calc_x_oai
