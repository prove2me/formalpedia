-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_12_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:28:22.295105+00:00
-- url     : https://prove2.me/submissions/d2b84dae-5b48-41a4-8a8a-79d547c470e9

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

lemma tr0_6_1_12_calc_x_oai (r : Fin 8) : taylorRowBox 0 6 1 12 r = tr0_6_1_12 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_12_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_12_calc_x_oai
