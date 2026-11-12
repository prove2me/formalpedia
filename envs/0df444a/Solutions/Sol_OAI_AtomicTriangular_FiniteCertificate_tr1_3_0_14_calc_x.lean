-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_14_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:49:43.645069+00:00
-- url     : https://prove2.me/submissions/39804885-7a89-4b85-a1dd-83ea12a07d13

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_3_0_14_calc_x_oai (r : Fin 8) : taylorRowBox 1 3 0 14 r = tr1_3_0_14 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_14_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_14_calc_x_oai
