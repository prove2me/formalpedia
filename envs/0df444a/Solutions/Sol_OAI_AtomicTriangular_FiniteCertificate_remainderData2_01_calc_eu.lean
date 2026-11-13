-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_01_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:42.656071+00:00
-- url     : https://prove2.me/submissions/30b69b24-5dc4-4aaa-b669-586bf8cf0fc6

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_01_calc_eu_oai (j : Fin 31) : remainderBox 0 1 2 j (taylorNormTable 0 1 j)=remainderData2_01 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_01_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_01_calc_eu_oai
