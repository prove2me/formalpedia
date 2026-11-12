-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD57_pre_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:38:30.216024+00:00
-- url     : https://prove2.me/submissions/c9287d3d-eab4-4ec7-96b2-37589f966296

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
lemma envelopeExpD57_pre_x_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 57))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD57_pre_x_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD57_pre_x_oai
