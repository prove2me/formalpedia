-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpB19_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:41:36.558735+00:00
-- url     : https://prove2.me/submissions/b8d1e8b2-1bb8-4e3e-9387-7982dbff015c

import Mathlib
import Definitions.Def_OAIQ334E000

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopePsiB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpB19_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 19))).exp.re=envelopeExpB19 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpB19_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpB19_calc_eu_oai
