-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:31:16.232953+00:00
-- url     : https://prove2.me/submissions/c3ed6323-164d-46e2-a54e-f85eb1657dbe

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
lemma remainderData6_11_calc_eu_oai (j : Fin 31) : remainderBox 1 1 6 j (taylorNormTable 1 1 j)=remainderData6_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData6_11_calc_eu_oai
