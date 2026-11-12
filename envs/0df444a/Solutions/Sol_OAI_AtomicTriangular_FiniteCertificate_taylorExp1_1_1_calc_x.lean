-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_1_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.596262+00:00
-- url     : https://prove2.me/submissions/d7cbafb6-e7f2-4901-8c0d-5c8c088cd27a

import Mathlib
import Definitions.Def_OAIQ257X020

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_1_calc_x_oai (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 1)).exp = taylorExp1_1_1 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_1_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_1_calc_x_oai
