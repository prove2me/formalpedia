-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_8_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:37:51.431856+00:00
-- url     : https://prove2.me/submissions/088795eb-6a6b-4555-b4cb-0d6794b47531

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_5_8_calc_x_oai (j : Fin 31) : taylorWaveBox 0 1 5 8 j = tw0_1_5_8 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_8_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_8_calc_x_oai
