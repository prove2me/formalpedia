-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:39:06.084192+00:00
-- url     : https://prove2.me/submissions/6a2a2dc3-7bd0-4124-a386-b44747cbb3b2

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008
import Definitions.Def_OAIQ257X020
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorPhase1_1_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_1_mem_x_oai (j : Fin 31) : (taylorExp1_1_1 j).Mem (exp (taylorPhase 1 1 (frequency j)*((1:ℤ):ℂ))) := by
  rw [← taylorExp1_1_1_calc_x]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase1_1_mem_x j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorExp1_1_1_mem_x_oai
