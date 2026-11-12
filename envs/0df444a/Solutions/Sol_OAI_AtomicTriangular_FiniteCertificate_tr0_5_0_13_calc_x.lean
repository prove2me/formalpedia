-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_13_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:45.078236+00:00
-- url     : https://prove2.me/submissions/0d17ea67-285b-47e8-95ae-79a3a51ccf8d

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

lemma tr0_5_0_13_calc_x_oai (r : Fin 8) : taylorRowBox 0 5 0 13 r = tr0_5_0_13 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_13_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_13_calc_x_oai
