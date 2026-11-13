-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.waveExpTable_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:06:41.517325+00:00
-- url     : https://prove2.me/submissions/e7090f6b-1b35-4e74-86f4-b5ea9d125dd4

import Mathlib
import Definitions.Def_OAIQ334E009
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_phaseHTable0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_19_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_21_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_9_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_16_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_19_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_21_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp1_9_mem_eu

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
lemma waveExp0_16_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 16)).exp = waveExp0_16 j := by
  revert j
  decide +kernel
lemma waveExp0_16_mem (j : Fin 31) : (waveExp0_16 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((16:ℤ):ℂ))) := by
  rw [← waveExp0_16_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem_eu j) (CI.mem_point 16)) (by
    revert j
    decide +kernel)
lemma waveExpTable_mem_eu_oai (q : Fin 2) (n : Fin 10) (j : Fin 31) : (waveExpTable q n j).Mem
    (exp (I*Real.pi*zeta (damping q) (damping 1) (frequency j)*(finiteNode n:ℂ))) := by
  fin_cases q <;> fin_cases n
  · exact waveExp0_1_mem_eu j
  · exact waveExp0_3_mem_eu j
  · exact waveExp0_4_mem_eu j
  · exact waveExp0_7_mem_eu j
  · exact waveExp0_9_mem_eu j
  · exact waveExp0_12_mem_eu j
  · exact waveExp0_13_mem_eu j
  · exact waveExp0_16_mem j
  · exact waveExp0_19_mem_eu j
  · exact waveExp0_21_mem_eu j
  · exact waveExp1_1_mem_eu j
  · exact waveExp1_3_mem_eu j
  · exact waveExp1_4_mem_eu j
  · exact waveExp1_7_mem_eu j
  · exact waveExp1_9_mem_eu j
  · exact waveExp1_12_mem_eu j
  · exact waveExp1_13_mem_eu j
  · exact waveExp1_16_mem_eu j
  · exact waveExp1_19_mem_eu j
  · exact waveExp1_21_mem_eu j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.waveExpTable_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.waveExpTable_mem_eu_oai
