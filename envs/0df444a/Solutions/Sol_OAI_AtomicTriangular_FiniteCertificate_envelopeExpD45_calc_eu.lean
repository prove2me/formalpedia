-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD45_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:55.971147+00:00
-- url     : https://prove2.me/submissions/be073410-217a-4ab9-8608-49502946812f

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
lemma envelopeExpD45_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 45))).exp.re=envelopeExpD45 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD45_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD45_calc_eu_oai
