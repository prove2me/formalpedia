-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:48:07.364786+00:00
-- url     : https://prove2.me/submissions/88522a95-71e2-418b-9ec7-4ab8d4347fdc

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_11_calc_x_oai (j : Fin 31) : remainderBox 1 1 6 j (taylorNormTable 1 1 j)=remainderData6_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_x_oai
