-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:47:39.232204+00:00
-- url     : https://prove2.me/submissions/437b2e62-da6d-401e-8883-999ee3745ff9

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
lemma remainderData6_01_calc_x_oai (j : Fin 31) : remainderBox 0 1 6 j (taylorNormTable 0 1 j)=remainderData6_01 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_calc_x_oai
