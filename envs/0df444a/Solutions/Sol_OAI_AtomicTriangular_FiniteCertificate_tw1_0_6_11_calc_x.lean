-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_11_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:52:01.429028+00:00
-- url     : https://prove2.me/submissions/3b4600b0-59de-484f-87aa-461954f4a8a3

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_6_11_calc_x_oai (j : Fin 31) : taylorWaveBox 1 0 6 11 j = tw1_0_6_11 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_11_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_11_calc_x_oai
