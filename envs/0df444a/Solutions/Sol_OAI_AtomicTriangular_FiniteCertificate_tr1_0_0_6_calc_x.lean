-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_6_calc_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:35:55.365762+00:00
-- url     : https://prove2.me/submissions/717b8b2b-d6f3-49a6-a10b-bf3bd4265ec2

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

lemma tr1_0_0_6_calc_x_oai (r : Fin 8) : taylorRowBox 1 0 0 6 r = tr1_0_0_6 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_6_calc_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_6_calc_x_oai
