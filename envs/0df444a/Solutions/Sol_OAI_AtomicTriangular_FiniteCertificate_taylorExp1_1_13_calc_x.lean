-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_13_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:04.142198+00:00
-- url     : https://prove2.me/submissions/2fdeb612-f63b-4551-8792-97e3ecbbd2d9

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
lemma taylorExp1_1_13_calc_x_oai (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 13)).exp = taylorExp1_1_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_13_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_13_calc_x_oai
