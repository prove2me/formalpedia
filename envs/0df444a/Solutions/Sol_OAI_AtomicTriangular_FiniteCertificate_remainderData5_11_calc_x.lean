-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData5_11_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:47:37.428475+00:00
-- url     : https://prove2.me/submissions/ef9ea609-5a44-44f2-99c6-6b9ffdd19b60

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData5_11_calc_x_oai (j : Fin 31) : remainderBox 1 1 5 j (taylorNormTable 1 1 j)=remainderData5_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData5_11_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData5_11_calc_x_oai
