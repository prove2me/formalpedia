-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData6_00_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:30:17.874651+00:00
-- url     : https://prove2.me/submissions/4a6f8285-8906-4014-a365-6e040c1d936d

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_00_calc_eu_oai (j : Fin 31) : remainderBox 0 0 6 j (taylorNormTable 0 0 j)=remainderData6_00 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData6_00_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData6_00_calc_eu_oai
