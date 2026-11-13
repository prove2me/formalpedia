-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:29:11.010995+00:00
-- url     : https://prove2.me/submissions/2a12440f-dadd-45e3-9635-353f6a40a513

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData3_10_calc_eu_oai (j : Fin 31) : remainderBox 1 0 3 j (taylorNormTable 1 0 j)=remainderData3_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_eu_oai
