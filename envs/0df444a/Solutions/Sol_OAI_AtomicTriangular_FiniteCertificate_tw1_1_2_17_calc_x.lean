-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_17_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:57:26.7632+00:00
-- url     : https://prove2.me/submissions/22872b12-3b9c-4aca-9226-137b8af04b36

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_2_17_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 2 17 j = tw1_1_2_17 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_17_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_17_calc_x_oai
