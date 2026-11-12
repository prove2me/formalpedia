-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_18_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:02:03.614693+00:00
-- url     : https://prove2.me/submissions/9ba8abdc-1412-4af7-975c-96ff740630e9

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

lemma tr0_2_1_18_calc_x_oai (r : Fin 8) : taylorRowBox 0 2 1 18 r = tr0_2_1_18 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_18_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_18_calc_x_oai
