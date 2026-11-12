-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp1_0_9_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:08.388296+00:00
-- url     : https://prove2.me/submissions/bbfd8fb1-4d57-411a-ac16-e0468f368893

import Mathlib
import Definitions.Def_OAIQ257X020

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_0_9_calc_x_oai (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 9)).exp = taylorExp1_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_0_9_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_0_9_calc_x_oai
