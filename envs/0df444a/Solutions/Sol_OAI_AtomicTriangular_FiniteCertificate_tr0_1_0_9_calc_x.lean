-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_9_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:55:36.769049+00:00
-- url     : https://prove2.me/submissions/daaaa0fd-50d6-47d2-a9b0-e3caf25aadc1

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

lemma tr0_1_0_9_calc_x_oai (r : Fin 8) : taylorRowBox 0 1 0 9 r = tr0_1_0_9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_9_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_9_calc_x_oai
