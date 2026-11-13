-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData5_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:30:16.594475+00:00
-- url     : https://prove2.me/submissions/6c558b6d-a18e-4654-af13-f514ae953842

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData5_10_calc_eu_oai (j : Fin 31) : remainderBox 1 0 5 j (taylorNormTable 1 0 j)=remainderData5_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData5_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData5_10_calc_eu_oai
