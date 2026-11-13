-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_6_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T14:04:07.187007+00:00
-- url     : https://prove2.me/submissions/8c1e7643-7ba4-48f2-875c-d8f7248d8c4e

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_0_6_calc_eu_oai (r : Fin 8) : taylorRowBox 1 6 0 6 r = tr1_6_0_6 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_6_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_6_calc_eu_oai
