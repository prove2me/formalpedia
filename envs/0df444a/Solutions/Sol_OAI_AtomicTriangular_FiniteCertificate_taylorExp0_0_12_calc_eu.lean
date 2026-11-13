-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_12_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:33:58.046078+00:00
-- url     : https://prove2.me/submissions/1825622e-552f-4251-ab11-0e0da720b277

import Mathlib
import Definitions.Def_OAIQ334E020

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_12_calc_eu_oai (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 12)).exp = taylorExp0_0_12 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_12_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_12_calc_eu_oai
