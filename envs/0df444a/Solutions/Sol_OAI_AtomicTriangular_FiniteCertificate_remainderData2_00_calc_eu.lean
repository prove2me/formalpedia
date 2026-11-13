-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:02.700051+00:00
-- url     : https://prove2.me/submissions/fbbfc2fd-512c-4751-a4b5-5c695171ee6c

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
lemma remainderData2_00_calc_eu_oai (j : Fin 31) : remainderBox 0 0 2 j (taylorNormTable 0 0 j)=remainderData2_00 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_calc_eu_oai
