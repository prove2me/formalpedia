-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_7_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:39:01.708426+00:00
-- url     : https://prove2.me/submissions/bf02ac30-1381-4e7c-a074-aba18ed696dc

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008
import Definitions.Def_OAIQ257X020
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorPhase0_0_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_7_mem_x_oai (j : Fin 31) : (taylorExp0_0_7 j).Mem (exp (taylorPhase 0 0 (frequency j)*((7:ℤ):ℂ))) := by
  rw [← taylorExp0_0_7_calc_x]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem_x j) (CI.mem_point 7)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_7_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp0_0_7_mem_x_oai
