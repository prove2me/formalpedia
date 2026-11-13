-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:29:46.126196+00:00
-- url     : https://prove2.me/submissions/8ce96855-a026-4032-9dba-f43a40c6d2a1

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData4_10_calc_eu_oai (j : Fin 31) : remainderBox 1 0 4 j (taylorNormTable 1 0 j)=remainderData4_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData4_10_calc_eu_oai
