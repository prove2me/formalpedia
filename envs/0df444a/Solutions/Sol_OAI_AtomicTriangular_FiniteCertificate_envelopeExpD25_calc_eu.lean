-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpD25_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:43:42.316345+00:00
-- url     : https://prove2.me/submissions/89819e53-3bdd-40bb-9d58-bd4cd26f19bb

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
lemma envelopeExpD25_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 25))).exp.re=envelopeExpD25 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD25_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpD25_calc_eu_oai
