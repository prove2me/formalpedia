-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_0_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:14:33.396442+00:00
-- url     : https://prove2.me/submissions/3e1263b7-1560-4a59-bf42-e64739861838

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_1_0_calc_x_oai (r : Fin 8) : taylorRowBox 1 6 1 0 r = tr1_6_1_0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_0_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_0_calc_x_oai
