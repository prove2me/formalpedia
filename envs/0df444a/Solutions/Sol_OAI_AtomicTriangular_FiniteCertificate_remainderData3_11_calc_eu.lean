-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData3_11_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:29:12.32343+00:00
-- url     : https://prove2.me/submissions/8d2b72c5-27b4-4d55-9691-079089c5f2f0

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData3_11_calc_eu_oai (j : Fin 31) : remainderBox 1 1 3 j (taylorNormTable 1 1 j)=remainderData3_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData3_11_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData3_11_calc_eu_oai
