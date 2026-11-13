-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:12:54.801435+00:00
-- url     : https://prove2.me/submissions/6463911f-b205-41a0-8dcf-0d5130653547

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_5_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_5_16_calc (j : Fin 31) : taylorWaveBox 1 0 5 16 j = tw1_0_5_16 j := by
  revert j
  decide +kernel
lemma tw1_0_5_17_calc (j : Fin 31) : taylorWaveBox 1 0 5 17 j = tw1_0_5_17 j := by
  revert j
  decide +kernel
lemma tw1_0_5_18_calc (j : Fin 31) : taylorWaveBox 1 0 5 18 j = tw1_0_5_18 j := by
  revert j
  decide +kernel
lemma tw1_0_5_19_calc (j : Fin 31) : taylorWaveBox 1 0 5 19 j = tw1_0_5_19 j := by
  revert j
  decide +kernel
lemma tw1_0_5_20_calc (j : Fin 31) : taylorWaveBox 1 0 5 20 j = tw1_0_5_20 j := by
  revert j
  decide +kernel
lemma tw1_0_5_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw1_0_5 l j).Mem (taylorWave 1 0 (nearNode 5) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 5 l j = tw1_0_5 l j := by
    fin_cases l
    · exact tw1_0_5_0_calc_eu j
    · exact tw1_0_5_1_calc_eu j
    · exact tw1_0_5_2_calc_eu j
    · exact tw1_0_5_3_calc_eu j
    · exact tw1_0_5_4_calc_eu j
    · exact tw1_0_5_5_calc_eu j
    · exact tw1_0_5_6_calc_eu j
    · exact tw1_0_5_7_calc_eu j
    · exact tw1_0_5_8_calc_eu j
    · exact tw1_0_5_9_calc_eu j
    · exact tw1_0_5_10_calc_eu j
    · exact tw1_0_5_11_calc_eu j
    · exact tw1_0_5_12_calc_eu j
    · exact tw1_0_5_13_calc_eu j
    · exact tw1_0_5_14_calc_eu j
    · exact tw1_0_5_15_calc_eu j
    · exact tw1_0_5_16_calc j
    · exact tw1_0_5_17_calc j
    · exact tw1_0_5_18_calc j
    · exact tw1_0_5_19_calc j
    · exact tw1_0_5_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 1 0 5 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_eu_oai
