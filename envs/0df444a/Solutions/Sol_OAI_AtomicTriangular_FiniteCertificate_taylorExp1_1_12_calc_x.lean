-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_12_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:39:33.675203+00:00
-- url     : https://prove2.me/submissions/3513c47e-9580-4c41-ab76-8be5de3cbe96

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
lemma taylorExp1_1_12_calc_x_oai (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 12)).exp = taylorExp1_1_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_12_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_12_calc_x_oai
