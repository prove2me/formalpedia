-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_3_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:08:03.211678+00:00
-- url     : https://prove2.me/submissions/df99baef-2fd5-4c86-b43e-dedcf346a814

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_3_1_3_calc_x_oai (r : Fin 8) : taylorRowBox 0 3 1 3 r = tr0_3_1_3 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_3_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_3_calc_x_oai
