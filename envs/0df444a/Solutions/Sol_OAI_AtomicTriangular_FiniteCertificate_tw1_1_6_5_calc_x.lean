-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_5_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:03:26.110499+00:00
-- url     : https://prove2.me/submissions/ff3a4ca0-4c99-4858-abbb-4fcf28cfe8f9

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
lemma tw1_1_6_5_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 6 5 j = tw1_1_6_5 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_5_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_5_calc_x_oai
