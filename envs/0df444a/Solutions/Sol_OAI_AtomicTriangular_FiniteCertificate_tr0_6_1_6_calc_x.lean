-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_6_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:30:45.874556+00:00
-- url     : https://prove2.me/submissions/58ab972b-367e-4394-8ef5-09eb868245f1

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_6_1_6_calc_x_oai (r : Fin 8) : taylorRowBox 0 6 1 6 r = tr0_6_1_6 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_6_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_6_calc_x_oai
