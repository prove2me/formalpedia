-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_9_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:54:45.969844+00:00
-- url     : https://prove2.me/submissions/04bb0a70-2bc0-483e-816d-825f60836e8f

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_0_9_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 0 9 j = tw1_1_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_9_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_9_calc_x_oai
