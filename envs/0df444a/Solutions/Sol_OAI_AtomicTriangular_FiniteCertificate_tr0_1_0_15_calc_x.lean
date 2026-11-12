-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_15_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:54:10.067932+00:00
-- url     : https://prove2.me/submissions/26b328e0-565f-49d2-8445-51fc52dc2ee2

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_1_0_15_calc_x_oai (r : Fin 8) : taylorRowBox 0 1 0 15 r = tr0_1_0_15 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_15_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_15_calc_x_oai
