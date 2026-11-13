-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:08:28.326404+00:00
-- url     : https://prove2.me/submissions/c14c6c31-8c92-4169-ba4a-afba305d95c2

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_2_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_2_16_calc (j : Fin 31) : taylorWaveBox 1 0 2 16 j = tw1_0_2_16 j := by
  revert j
  decide +kernel
lemma tw1_0_2_17_calc (j : Fin 31) : taylorWaveBox 1 0 2 17 j = tw1_0_2_17 j := by
  revert j
  decide +kernel
lemma tw1_0_2_18_calc (j : Fin 31) : taylorWaveBox 1 0 2 18 j = tw1_0_2_18 j := by
  revert j
  decide +kernel
lemma tw1_0_2_19_calc (j : Fin 31) : taylorWaveBox 1 0 2 19 j = tw1_0_2_19 j := by
  revert j
  decide +kernel
lemma tw1_0_2_20_calc (j : Fin 31) : taylorWaveBox 1 0 2 20 j = tw1_0_2_20 j := by
  revert j
  decide +kernel
lemma tw1_0_2_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw1_0_2 l j).Mem (taylorWave 1 0 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 2 l j = tw1_0_2 l j := by
    fin_cases l
    · exact tw1_0_2_0_calc_eu j
    · exact tw1_0_2_1_calc_eu j
    · exact tw1_0_2_2_calc_eu j
    · exact tw1_0_2_3_calc_eu j
    · exact tw1_0_2_4_calc_eu j
    · exact tw1_0_2_5_calc_eu j
    · exact tw1_0_2_6_calc_eu j
    · exact tw1_0_2_7_calc_eu j
    · exact tw1_0_2_8_calc_eu j
    · exact tw1_0_2_9_calc_eu j
    · exact tw1_0_2_10_calc_eu j
    · exact tw1_0_2_11_calc_eu j
    · exact tw1_0_2_12_calc_eu j
    · exact tw1_0_2_13_calc_eu j
    · exact tw1_0_2_14_calc_eu j
    · exact tw1_0_2_15_calc_eu j
    · exact tw1_0_2_16_calc j
    · exact tw1_0_2_17_calc j
    · exact tw1_0_2_18_calc j
    · exact tw1_0_2_19_calc j
    · exact tw1_0_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 1 0 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_eu_oai
