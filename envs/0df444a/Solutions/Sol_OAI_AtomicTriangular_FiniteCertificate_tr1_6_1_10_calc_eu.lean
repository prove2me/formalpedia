-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_10_calc_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:21:24.435192+00:00
-- url     : https://prove2.me/submissions/cf78310d-77e2-40b3-ad2c-cb9a877a9b26

import Mathlib
import Definitions.Def_OAIQ334E023

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_1_10_calc_eu_oai (r : Fin 8) : taylorRowBox 1 6 1 10 r = tr1_6_1_10 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_10_calc_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_10_calc_eu_oai
