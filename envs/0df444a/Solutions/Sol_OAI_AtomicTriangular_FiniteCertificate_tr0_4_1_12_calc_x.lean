-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_4_1_12_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:13:33.33106+00:00
-- url     : https://prove2.me/submissions/d0dcb886-9299-446d-a22d-85916bf44b3d

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_4_1_12_calc_x_oai (r : Fin 8) : taylorRowBox 0 4 1 12 r = tr0_4_1_12 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_4_1_12_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_4_1_12_calc_x_oai
