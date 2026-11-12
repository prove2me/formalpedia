-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_4_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:34:42.657795+00:00
-- url     : https://prove2.me/submissions/9f0beda5-302f-4b4a-be51-266b7924f6a1

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_0_0_4_calc_x_oai (r : Fin 8) : taylorRowBox 1 0 0 4 r = tr1_0_0_4 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_4_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_4_calc_x_oai
