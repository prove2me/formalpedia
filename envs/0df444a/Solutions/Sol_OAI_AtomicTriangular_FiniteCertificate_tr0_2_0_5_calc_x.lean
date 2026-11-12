-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_5_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:59:44.083053+00:00
-- url     : https://prove2.me/submissions/0343d8ba-00fa-4917-ab39-d1103b216eef

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

lemma tr0_2_0_5_calc_x_oai (r : Fin 8) : taylorRowBox 0 2 0 5 r = tr0_2_0_5 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_5_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_5_calc_x_oai
