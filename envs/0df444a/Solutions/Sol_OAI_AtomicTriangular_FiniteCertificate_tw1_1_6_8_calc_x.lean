-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_8_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:03:28.611493+00:00
-- url     : https://prove2.me/submissions/4dc50758-e5a0-4fa2-ad04-7809ba76ab04

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_6_8_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 6 8 j = tw1_1_6_8 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_8_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_8_calc_x_oai
