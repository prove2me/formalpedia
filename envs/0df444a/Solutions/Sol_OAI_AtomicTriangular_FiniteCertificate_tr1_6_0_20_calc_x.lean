-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_20_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:14:30.684613+00:00
-- url     : https://prove2.me/submissions/d493a163-268d-4d18-9478-ccb048b42934

import Mathlib
import Definitions.Def_OAIQ257X023

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_0_20_calc_x_oai (r : Fin 8) : taylorRowBox 1 6 0 20 r = tr1_6_0_20 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_20_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_20_calc_x_oai
