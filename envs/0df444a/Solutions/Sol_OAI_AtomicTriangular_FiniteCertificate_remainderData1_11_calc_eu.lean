-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData1_11_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:28:36.166224+00:00
-- url     : https://prove2.me/submissions/353817cd-b68c-40c9-9ebf-a3a2da9194f6

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData1_11_calc_eu_oai (j : Fin 31) : remainderBox 1 1 1 j (taylorNormTable 1 1 j)=remainderData1_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData1_11_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData1_11_calc_eu_oai
