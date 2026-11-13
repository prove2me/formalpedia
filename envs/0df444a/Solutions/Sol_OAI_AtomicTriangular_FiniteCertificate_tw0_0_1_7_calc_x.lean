-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_7_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:21:10.907591+00:00
-- url     : https://prove2.me/submissions/c248d1a6-cb9e-4da8-93bc-10d991cb7992

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_1_7_calc_x_oai (j : Fin 31) : taylorWaveBox 0 0 1 7 j = tw0_0_1_7 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_7_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_7_calc_x_oai
