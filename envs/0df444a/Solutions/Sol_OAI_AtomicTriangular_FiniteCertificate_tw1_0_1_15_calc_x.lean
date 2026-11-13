-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_15_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:42:20.23548+00:00
-- url     : https://prove2.me/submissions/858608cb-6a2b-4d04-b0ef-ff7ea51f9b45

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_1_15_calc_x_oai (j : Fin 31) : taylorWaveBox 1 0 1 15 j = tw1_0_1_15 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_15_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_15_calc_x_oai
