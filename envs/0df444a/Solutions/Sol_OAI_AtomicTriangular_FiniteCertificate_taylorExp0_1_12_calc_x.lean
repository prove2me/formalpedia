-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp0_1_12_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:37:37.837398+00:00
-- url     : https://prove2.me/submissions/817f0f7c-919d-43f2-97e2-8149d81c2388

import Mathlib
import Definitions.Def_OAIQ257X020

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_1_12_calc_x_oai (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 12)).exp = taylorExp0_1_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_1_12_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_1_12_calc_x_oai
