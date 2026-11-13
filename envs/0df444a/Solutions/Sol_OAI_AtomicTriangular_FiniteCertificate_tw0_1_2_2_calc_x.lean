-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_2_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:11.796298+00:00
-- url     : https://prove2.me/submissions/50a3939d-fa7a-4965-860c-2a15f535a2ac

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_2_2_calc_x_oai (j : Fin 31) : taylorWaveBox 0 1 2 2 j = tw0_1_2_2 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_2_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_2_calc_x_oai
