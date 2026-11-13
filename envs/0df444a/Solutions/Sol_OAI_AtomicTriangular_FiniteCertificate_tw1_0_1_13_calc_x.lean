-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_13_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:42:17.53698+00:00
-- url     : https://prove2.me/submissions/f4b3320c-02b0-4acb-a5c9-18f7482d5408

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
lemma tw1_0_1_13_calc_x_oai (j : Fin 31) : taylorWaveBox 1 0 1 13 j = tw1_0_1_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_13_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_13_calc_x_oai
