-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_15_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:59:55.955849+00:00
-- url     : https://prove2.me/submissions/c333fcca-2c30-4fcd-93b8-5100ffc4ed2d

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_4_15_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 4 15 j = tw1_1_4_15 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_15_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_15_calc_x_oai
