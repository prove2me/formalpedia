-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_0_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:28:11.371861+00:00
-- url     : https://prove2.me/submissions/ae53b657-766d-4ad0-bab6-94c7f0656a05

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_0_0_calc_x_oai (j : Fin 31) : taylorWaveBox 0 1 0 0 j = tw0_1_0_0 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_0_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_0_calc_x_oai
