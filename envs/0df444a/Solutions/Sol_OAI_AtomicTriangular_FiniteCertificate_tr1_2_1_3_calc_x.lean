-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_3_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:48:43.27401+00:00
-- url     : https://prove2.me/submissions/82e874aa-e12c-49a4-8228-ff1bc222be6e

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_2_1_3_calc_x_oai (r : Fin 8) : taylorRowBox 1 2 1 3 r = tr1_2_1_3 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_3_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_3_calc_x_oai
