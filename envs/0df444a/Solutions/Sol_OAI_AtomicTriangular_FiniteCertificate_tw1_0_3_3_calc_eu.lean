-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_3_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:09:31.774284+00:00
-- url     : https://prove2.me/submissions/a50b8d1e-b5b1-4386-ae82-ea641e4bd024

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_3_calc_eu_oai (j : Fin 31) : taylorWaveBox 1 0 3 3 j = tw1_0_3_3 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_3_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_3_calc_eu_oai
