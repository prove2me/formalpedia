-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:14:26.559041+00:00
-- url     : https://prove2.me/submissions/029226b5-640c-4fcd-9849-912de6eb5392

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_6_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_6_16_calc (j : Fin 31) : taylorWaveBox 1 0 6 16 j = tw1_0_6_16 j := by
  revert j
  decide +kernel
lemma tw1_0_6_17_calc (j : Fin 31) : taylorWaveBox 1 0 6 17 j = tw1_0_6_17 j := by
  revert j
  decide +kernel
lemma tw1_0_6_18_calc (j : Fin 31) : taylorWaveBox 1 0 6 18 j = tw1_0_6_18 j := by
  revert j
  decide +kernel
lemma tw1_0_6_19_calc (j : Fin 31) : taylorWaveBox 1 0 6 19 j = tw1_0_6_19 j := by
  revert j
  decide +kernel
lemma tw1_0_6_20_calc (j : Fin 31) : taylorWaveBox 1 0 6 20 j = tw1_0_6_20 j := by
  revert j
  decide +kernel
lemma tw1_0_6_mem (l : Fin 21) (j : Fin 31) : (tw1_0_6 l j).Mem (taylorWave 1 0 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 6 l j = tw1_0_6 l j := by
    fin_cases l
    · exact tw1_0_6_0_calc_eu j
    · exact tw1_0_6_1_calc_eu j
    · exact tw1_0_6_2_calc_eu j
    · exact tw1_0_6_3_calc_eu j
    · exact tw1_0_6_4_calc_eu j
    · exact tw1_0_6_5_calc_eu j
    · exact tw1_0_6_6_calc_eu j
    · exact tw1_0_6_7_calc_eu j
    · exact tw1_0_6_8_calc_eu j
    · exact tw1_0_6_9_calc_eu j
    · exact tw1_0_6_10_calc_eu j
    · exact tw1_0_6_11_calc_eu j
    · exact tw1_0_6_12_calc_eu j
    · exact tw1_0_6_13_calc_eu j
    · exact tw1_0_6_14_calc_eu j
    · exact tw1_0_6_15_calc_eu j
    · exact tw1_0_6_16_calc j
    · exact tw1_0_6_17_calc j
    · exact tw1_0_6_18_calc j
    · exact tw1_0_6_19_calc j
    · exact tw1_0_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 1 0 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_mem_eu_oai (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_0 n l j).Mem (taylorWave 1 0 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_0_0_mem_eu l j
  · exact tw1_0_1_mem_eu l j
  · exact tw1_0_2_mem_eu l j
  · exact tw1_0_3_mem_eu l j
  · exact tw1_0_4_mem_eu l j
  · exact tw1_0_5_mem_eu l j
  · exact tw1_0_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_eu_oai
