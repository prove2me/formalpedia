-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:39:21.843864+00:00
-- url     : https://prove2.me/submissions/ceda854c-786b-4c32-9a0e-407172640701

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
lemma envelopeExpB16_calc_eu_oai (j : Fin 31) : (CI.ofReal (((envelopePhase01 j).re.neg).neg.mul (RI.point 16))).exp.re=envelopeExpB16 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_calc_eu_oai
