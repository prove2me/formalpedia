-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_7_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:03:05.073011+00:00
-- url     : https://prove2.me/submissions/e302e5d0-64b1-4613-8cd7-fea7c2076dfc

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_2_1_7_calc_x_oai (r : Fin 8) : taylorRowBox 0 2 1 7 r = tr0_2_1_7 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_7_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_7_calc_x_oai
