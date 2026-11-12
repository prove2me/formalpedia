-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_7_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:31:14.186272+00:00
-- url     : https://prove2.me/submissions/b4853d8b-1046-4891-b7c4-4e20630f344f

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

lemma tr0_6_1_7_calc_x_oai (r : Fin 8) : taylorRowBox 0 6 1 7 r = tr0_6_1_7 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_7_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_7_calc_x_oai
