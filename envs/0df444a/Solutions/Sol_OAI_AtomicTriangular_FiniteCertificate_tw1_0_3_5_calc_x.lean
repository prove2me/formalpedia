-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_5_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:47:31.106507+00:00
-- url     : https://prove2.me/submissions/2680539d-b1a4-490b-8848-80f0a82da112

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_5_calc_x_oai (j : Fin 31) : taylorWaveBox 1 0 3 5 j = tw1_0_3_5 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_5_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_5_calc_x_oai
