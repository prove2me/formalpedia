-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:42:09.196354+00:00
-- url     : https://prove2.me/submissions/5b821d4d-d1d0-4557-8f9d-b85290fa0444

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_1_1_10_calc_x_oai (r : Fin 8) : taylorRowBox 1 1 1 10 r = tr1_1_1_10 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_10_calc_x_oai
