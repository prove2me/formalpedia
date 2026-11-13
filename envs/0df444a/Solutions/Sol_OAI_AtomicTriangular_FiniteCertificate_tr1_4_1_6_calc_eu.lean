-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_6_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:51:46.494785+00:00
-- url     : https://prove2.me/submissions/bca41dd4-7ca6-4602-b448-5b216244389f

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_4_1_6_calc_eu_oai (r : Fin 8) : taylorRowBox 1 4 1 6 r = tr1_4_1_6 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_6_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_6_calc_eu_oai
