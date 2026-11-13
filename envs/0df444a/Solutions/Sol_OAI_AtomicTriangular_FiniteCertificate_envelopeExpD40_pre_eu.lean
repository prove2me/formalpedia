-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD40_pre_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:54.950104+00:00
-- url     : https://prove2.me/submissions/f102390c-cccd-4e3d-9a44-152f4950ddd3

import Mathlib
import Definitions.Def_OAIQ334E004

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpD40_pre_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 40))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD40_pre_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD40_pre_eu_oai
