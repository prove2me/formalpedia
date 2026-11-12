-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:44:24.025992+00:00
-- url     : https://prove2.me/submissions/26421423-104e-49de-b210-5dbfe85eade6

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_10_calc_x_oai (j : Fin 31) : remainderBox 1 0 2 j (taylorNormTable 1 0 j)=remainderData2_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_10_calc_x_oai
