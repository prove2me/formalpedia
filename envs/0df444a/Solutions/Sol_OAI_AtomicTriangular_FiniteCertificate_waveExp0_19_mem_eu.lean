-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.waveExp0_19_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:00:43.404176+00:00
-- url     : https://prove2.me/submissions/4c6f3d44-fad8-4889-87a0-c44b47ba3705

import Mathlib
import Definitions.Def_OAIQ334E009
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_phaseHTable0_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma waveExp0_19_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 19)).exp = waveExp0_19 j := by
  revert j
  decide +kernel
lemma waveExp0_19_mem_eu_oai (j : Fin 31) : (waveExp0_19 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((19:ℤ):ℂ))) := by
  rw [← waveExp0_19_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem_eu j) (CI.mem_point 19)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.waveExp0_19_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.waveExp0_19_mem_eu_oai
