-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:29:47.217184+00:00
-- url     : https://prove2.me/submissions/eb2f739e-7ccd-455f-9144-59cdf1f4db78

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
lemma remainderData4_11_calc_eu_oai (j : Fin 31) : remainderBox 1 1 4 j (taylorNormTable 1 1 j)=remainderData4_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData4_11_calc_eu_oai
