-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:01:21.338581+00:00
-- url     : https://prove2.me/submissions/3ece477c-d87f-4726-8589-70fc215afbbe

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_5_10_calc_x_oai (j : Fin 31) : taylorWaveBox 1 1 5 10 j = tw1_1_5_10 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_10_calc_x_oai
