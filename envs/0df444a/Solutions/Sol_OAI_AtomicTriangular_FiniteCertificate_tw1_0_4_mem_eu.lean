-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:11:22.826148+00:00
-- url     : https://prove2.me/submissions/877a11e8-d9e0-4a8d-b8c0-3bd9e16e8534

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_4_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_4_16_calc (j : Fin 31) : taylorWaveBox 1 0 4 16 j = tw1_0_4_16 j := by
  revert j
  decide +kernel
lemma tw1_0_4_17_calc (j : Fin 31) : taylorWaveBox 1 0 4 17 j = tw1_0_4_17 j := by
  revert j
  decide +kernel
lemma tw1_0_4_18_calc (j : Fin 31) : taylorWaveBox 1 0 4 18 j = tw1_0_4_18 j := by
  revert j
  decide +kernel
lemma tw1_0_4_19_calc (j : Fin 31) : taylorWaveBox 1 0 4 19 j = tw1_0_4_19 j := by
  revert j
  decide +kernel
lemma tw1_0_4_20_calc (j : Fin 31) : taylorWaveBox 1 0 4 20 j = tw1_0_4_20 j := by
  revert j
  decide +kernel
lemma tw1_0_4_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw1_0_4 l j).Mem (taylorWave 1 0 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 4 l j = tw1_0_4 l j := by
    fin_cases l
    · exact tw1_0_4_0_calc_eu j
    · exact tw1_0_4_1_calc_eu j
    · exact tw1_0_4_2_calc_eu j
    · exact tw1_0_4_3_calc_eu j
    · exact tw1_0_4_4_calc_eu j
    · exact tw1_0_4_5_calc_eu j
    · exact tw1_0_4_6_calc_eu j
    · exact tw1_0_4_7_calc_eu j
    · exact tw1_0_4_8_calc_eu j
    · exact tw1_0_4_9_calc_eu j
    · exact tw1_0_4_10_calc_eu j
    · exact tw1_0_4_11_calc_eu j
    · exact tw1_0_4_12_calc_eu j
    · exact tw1_0_4_13_calc_eu j
    · exact tw1_0_4_14_calc_eu j
    · exact tw1_0_4_15_calc_eu j
    · exact tw1_0_4_16_calc j
    · exact tw1_0_4_17_calc j
    · exact tw1_0_4_18_calc j
    · exact tw1_0_4_19_calc j
    · exact tw1_0_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 1 0 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_eu_oai
