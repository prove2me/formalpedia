-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:28:37.232707+00:00
-- url     : https://prove2.me/submissions/4c33683a-2ced-42af-a2e3-3700850feb9a

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
lemma remainderData2_11_calc_eu_oai (j : Fin 31) : remainderBox 1 1 2 j (taylorNormTable 1 1 j)=remainderData2_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_11_calc_eu_oai
