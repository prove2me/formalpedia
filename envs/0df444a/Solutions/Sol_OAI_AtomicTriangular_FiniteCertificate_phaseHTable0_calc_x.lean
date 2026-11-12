-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.phaseHTable0_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:41.203579+00:00
-- url     : https://prove2.me/submissions/7bb995c3-c214-445e-a5ba-5c158dddece9

import Mathlib
import Definitions.Def_OAIQ257X008

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma phaseHTable0_calc_x_oai (j : Fin 31) : wavePhaseBox 0 1 j = phaseHTable0 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.phaseHTable0_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.phaseHTable0_calc_x_oai
