-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:58:03.751818+00:00
-- url     : https://prove2.me/submissions/9f22b00f-0b40-487e-99a4-652b93b48ee5

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_2_16_calc (j : Fin 31) : taylorWaveBox 0 1 2 16 j = tw0_1_2_16 j := by
  revert j
  decide +kernel
lemma tw0_1_2_17_calc (j : Fin 31) : taylorWaveBox 0 1 2 17 j = tw0_1_2_17 j := by
  revert j
  decide +kernel
lemma tw0_1_2_18_calc (j : Fin 31) : taylorWaveBox 0 1 2 18 j = tw0_1_2_18 j := by
  revert j
  decide +kernel
lemma tw0_1_2_19_calc (j : Fin 31) : taylorWaveBox 0 1 2 19 j = tw0_1_2_19 j := by
  revert j
  decide +kernel
lemma tw0_1_2_20_calc (j : Fin 31) : taylorWaveBox 0 1 2 20 j = tw0_1_2_20 j := by
  revert j
  decide +kernel
lemma tw0_1_2_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_1_2 l j).Mem (taylorWave 0 1 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 2 l j = tw0_1_2 l j := by
    fin_cases l
    · exact tw0_1_2_0_calc_eu j
    · exact tw0_1_2_1_calc_eu j
    · exact tw0_1_2_2_calc_eu j
    · exact tw0_1_2_3_calc_eu j
    · exact tw0_1_2_4_calc_eu j
    · exact tw0_1_2_5_calc_eu j
    · exact tw0_1_2_6_calc_eu j
    · exact tw0_1_2_7_calc_eu j
    · exact tw0_1_2_8_calc_eu j
    · exact tw0_1_2_9_calc_eu j
    · exact tw0_1_2_10_calc_eu j
    · exact tw0_1_2_11_calc_eu j
    · exact tw0_1_2_12_calc_eu j
    · exact tw0_1_2_13_calc_eu j
    · exact tw0_1_2_14_calc_eu j
    · exact tw0_1_2_15_calc_eu j
    · exact tw0_1_2_16_calc j
    · exact tw0_1_2_17_calc j
    · exact tw0_1_2_18_calc j
    · exact tw0_1_2_19_calc j
    · exact tw0_1_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 1 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_eu_oai
