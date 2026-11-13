-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_3_16_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:58:28.86323+00:00
-- url     : https://prove2.me/submissions/7b79dff2-e812-41ef-b558-cfb4fc1512e4

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_3_16_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 3 16 j = tw1_1_3_16 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_3_16_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_3_16_calc_x_oai
