-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_1_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:45:07.07596+00:00
-- url     : https://prove2.me/submissions/dbc5e86b-d933-4453-a0d1-b42f011c9652

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_2_1_calc_x_oai (j : Fin 31) : taylorWaveBox 1 0 2 1 j = tw1_0_2_1 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_1_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_1_calc_x_oai
