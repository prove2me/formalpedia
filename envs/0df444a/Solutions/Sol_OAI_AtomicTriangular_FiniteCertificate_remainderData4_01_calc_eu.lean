-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData4_01_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:29:44.778323+00:00
-- url     : https://prove2.me/submissions/f937b4f0-e8ca-4a15-b376-5fc63d8cccb0

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData4_01_calc_eu_oai (j : Fin 31) : remainderBox 0 1 4 j (taylorNormTable 0 1 j)=remainderData4_01 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData4_01_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData4_01_calc_eu_oai
