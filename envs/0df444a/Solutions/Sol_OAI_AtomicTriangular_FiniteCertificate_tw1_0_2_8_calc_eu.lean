-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_8_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:07:56.872205+00:00
-- url     : https://prove2.me/submissions/32f81302-5ee1-4e69-bc6e-587cc5e6d2b1

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_2_8_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 2 8 j = tw1_0_2_8 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_8_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_8_calc_eu_oai
