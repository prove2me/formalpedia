-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_15_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:18:23.685334+00:00
-- url     : https://prove2.me/submissions/73e43954-fa59-4e54-8ed0-48faecafcfe7

import Mathlib
import Definitions.Def_OAIQ257X025

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_15_calc_x_oai (j : Fin 31) : taylorWaveBox 0 0 0 15 j = tw0_0_0_15 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_15_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_15_calc_x_oai
