-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD40_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:54.108223+00:00
-- url     : https://prove2.me/submissions/49aa66d6-8df4-46d1-9eb1-5f07f4b950da

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
lemma envelopeExpD40_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 40))).exp.re=envelopeExpD40 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD40_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD40_calc_eu_oai
