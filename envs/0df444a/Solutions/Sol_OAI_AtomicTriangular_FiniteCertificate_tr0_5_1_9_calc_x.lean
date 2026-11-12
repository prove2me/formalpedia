-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_9_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:41.915224+00:00
-- url     : https://prove2.me/submissions/b3579f98-2845-4e9e-8956-ab84d1b733a2

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

lemma tr0_5_1_9_calc_x_oai (r : Fin 8) : taylorRowBox 0 5 1 9 r = tr0_5_1_9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_9_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_9_calc_x_oai
