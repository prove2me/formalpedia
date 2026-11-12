-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:47:33.053266+00:00
-- url     : https://prove2.me/submissions/8b720104-81a5-41be-80ff-392072c1b92d

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
lemma remainderData5_00_calc_x_oai (j : Fin 31) : remainderBox 0 0 5 j (taylorNormTable 0 0 j)=remainderData5_00 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_x_oai
