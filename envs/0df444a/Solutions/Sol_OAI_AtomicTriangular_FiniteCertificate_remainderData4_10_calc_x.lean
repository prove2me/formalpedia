-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:47:06.463712+00:00
-- url     : https://prove2.me/submissions/29e12b58-15f7-4c3a-84ee-481f6404dd01

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData4_10_calc_x_oai (j : Fin 31) : remainderBox 1 0 4 j (taylorNormTable 1 0 j)=remainderData4_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_x_oai
