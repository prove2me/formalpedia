-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:03:10.912206+00:00
-- url     : https://prove2.me/submissions/e40fbc83-2ff1-4a5f-be33-e390485c67f9

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_10_calc_eu_oai (j : Fin 31) : remainderBox 1 0 2 j (taylorNormTable 1 0 j)=remainderData2_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_eu_oai
