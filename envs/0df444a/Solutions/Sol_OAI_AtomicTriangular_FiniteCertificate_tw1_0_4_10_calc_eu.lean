-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:10:10.82746+00:00
-- url     : https://prove2.me/submissions/6b01c584-c216-4e5e-a676-8dbcc8a3a3d2

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_4_10_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 4 10 j = tw1_0_4_10 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_10_calc_eu_oai
