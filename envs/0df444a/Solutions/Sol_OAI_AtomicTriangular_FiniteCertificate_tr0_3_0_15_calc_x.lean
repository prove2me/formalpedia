-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_3_0_15_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:04:09.28506+00:00
-- url     : https://prove2.me/submissions/0ddb8cda-de32-41c6-9090-cbb5e87fc130

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_3_0_15_calc_x_oai (r : Fin 8) : taylorRowBox 0 3 0 15 r = tr0_3_0_15 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_3_0_15_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_3_0_15_calc_x_oai
