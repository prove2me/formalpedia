-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:01:57.380542+00:00
-- url     : https://prove2.me/submissions/1d851808-a42a-478c-9363-97dcd5a2bc32

import Mathlib
import Definitions.Def_OAIQ334E021

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_1_calc_eu_oai (j : Fin 31) : curvatureBox 0 1 1 j=curvatureData01_1 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_calc_eu_oai
