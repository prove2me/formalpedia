-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:44:26.510202+00:00
-- url     : https://prove2.me/submissions/0390ce37-0cac-4660-80a5-4976b28f4c9e

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
lemma remainderData2_11_calc_x_oai (j : Fin 31) : remainderBox 1 1 2 j (taylorNormTable 1 1 j)=remainderData2_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_x_oai
