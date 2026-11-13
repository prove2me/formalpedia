-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD39_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:32.141202+00:00
-- url     : https://prove2.me/submissions/e491fa34-4a46-48cc-8c6a-4f21ccd8b04d

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
lemma envelopeExpD39_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 39))).exp.re=envelopeExpD39 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD39_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD39_calc_eu_oai
