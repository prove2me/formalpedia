-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_10_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:28.195076+00:00
-- url     : https://prove2.me/submissions/169f9bf1-a36e-4451-9abd-9212b1941d59

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

lemma tr1_2_0_10_calc_x_oai (r : Fin 8) : taylorRowBox 1 2 0 10 r = tr1_2_0_10 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_10_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_10_calc_x_oai
