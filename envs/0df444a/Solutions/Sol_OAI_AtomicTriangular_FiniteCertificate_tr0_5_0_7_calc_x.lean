-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_7_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:19:43.035075+00:00
-- url     : https://prove2.me/submissions/015cb16d-85f6-49ae-bb1b-a455b7109a2e

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_5_0_7_calc_x_oai (r : Fin 8) : taylorRowBox 0 5 0 7 r = tr0_5_0_7 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_7_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_7_calc_x_oai
