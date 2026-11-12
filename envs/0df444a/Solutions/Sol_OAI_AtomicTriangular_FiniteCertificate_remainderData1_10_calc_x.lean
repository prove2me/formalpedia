-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:43:50.680129+00:00
-- url     : https://prove2.me/submissions/3892fe46-98aa-4196-a40f-7681ff0b4389

import Mathlib
import Definitions.Def_OAIQ257X021

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData1_10_calc_x_oai (j : Fin 31) : remainderBox 1 0 1 j (taylorNormTable 1 0 j)=remainderData1_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData1_10_calc_x_oai
