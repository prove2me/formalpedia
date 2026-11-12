-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_4_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:06.120772+00:00
-- url     : https://prove2.me/submissions/87271382-a718-4193-a9e5-2b8b973fcf7e

import Mathlib
import Definitions.Def_OAIQ257X020

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_4_calc_x_oai (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 4)).exp = taylorExp0_0_4 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_4_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_4_calc_x_oai
