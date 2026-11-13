-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_6_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:37:50.634006+00:00
-- url     : https://prove2.me/submissions/575f0a3f-3a5c-4cb5-9bc9-185bcaaa4725

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_2_0_6_calc_eu_oai (r : Fin 8) : taylorRowBox 0 2 0 6 r = tr0_2_0_6 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_6_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_6_calc_eu_oai
