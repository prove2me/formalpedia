-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD55_pre_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:38:01.770476+00:00
-- url     : https://prove2.me/submissions/15adb724-6734-44f7-90a8-c1c77732e3ec

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
lemma envelopeExpD55_pre_x_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 55))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD55_pre_x_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD55_pre_x_oai
