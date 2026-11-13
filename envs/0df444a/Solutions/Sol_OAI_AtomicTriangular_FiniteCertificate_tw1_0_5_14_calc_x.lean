-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_14_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:50:56.060197+00:00
-- url     : https://prove2.me/submissions/8d382514-b919-46bc-9bcb-6f550364db9f

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_5_14_calc_x_oai (j : Fin 31) : taylorWaveBox 1 0 5 14 j = tw1_0_5_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_14_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_14_calc_x_oai
