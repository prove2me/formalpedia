-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_1_0_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:28:18.636489+00:00
-- url     : https://prove2.me/submissions/c9f6b9ba-c3ba-40d6-a995-acf52e970fdf

import Mathlib
import Definitions.Def_OAIQ334E025

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_1_0_calc_eu_oai (j : Fin 31) : taylorWaveBox 0 1 1 0 j = tw0_1_1_0 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_1_0_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_1_0_calc_eu_oai
