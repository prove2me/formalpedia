-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp1_0_9_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:34:00.116019+00:00
-- url     : https://prove2.me/submissions/99f84cb0-9c3d-42b1-9cc7-b6635b2112a3

import Mathlib
import Definitions.Def_OAIQ334E020

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorExp10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_0_9_calc_eu_oai (j : Fin 31) : ((taylorPhase1_0 j).mul (CI.point 9)).exp = taylorExp1_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_0_9_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_0_9_calc_eu_oai
