-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_0_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:12:55.759654+00:00
-- url     : https://prove2.me/submissions/2b2e10e3-bdfd-4208-9c29-851bc7ba739b

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_6_0_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 6 0 j = tw1_0_6_0 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_0_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_6_0_calc_eu_oai
