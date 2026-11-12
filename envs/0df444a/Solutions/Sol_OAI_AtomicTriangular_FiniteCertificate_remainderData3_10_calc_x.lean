-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:46:09.198468+00:00
-- url     : https://prove2.me/submissions/f939ea83-cf51-46ac-8cdd-733b32d505c5

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData3_10_calc_x_oai (j : Fin 31) : remainderBox 1 0 3 j (taylorNormTable 1 0 j)=remainderData3_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData3_10_calc_x_oai
