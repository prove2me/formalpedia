-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:03:11.935527+00:00
-- url     : https://prove2.me/submissions/fde8c55c-ac0e-456f-800e-33d9df08e610

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
lemma remainderData5_00_calc_eu_oai (j : Fin 31) : remainderBox 0 0 5 j (taylorNormTable 0 0 j)=remainderData5_00 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData5_00_calc_eu_oai
