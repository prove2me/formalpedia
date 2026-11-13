-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:00:55.68533+00:00
-- url     : https://prove2.me/submissions/9fd9c24b-2372-43de-9550-95d5f6e0b439

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_4_16_calc (j : Fin 31) : taylorWaveBox 1 1 4 16 j = tw1_1_4_16 j := by
  revert j
  decide +kernel
lemma tw1_1_4_17_calc (j : Fin 31) : taylorWaveBox 1 1 4 17 j = tw1_1_4_17 j := by
  revert j
  decide +kernel
lemma tw1_1_4_18_calc (j : Fin 31) : taylorWaveBox 1 1 4 18 j = tw1_1_4_18 j := by
  revert j
  decide +kernel
lemma tw1_1_4_19_calc (j : Fin 31) : taylorWaveBox 1 1 4 19 j = tw1_1_4_19 j := by
  revert j
  decide +kernel
lemma tw1_1_4_20_calc (j : Fin 31) : taylorWaveBox 1 1 4 20 j = tw1_1_4_20 j := by
  revert j
  decide +kernel
lemma tw1_1_4_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw1_1_4 l j).Mem (taylorWave 1 1 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 4 l j = tw1_1_4 l j := by
    fin_cases l
    · exact tw1_1_4_0_calc_x j
    · exact tw1_1_4_1_calc_x j
    · exact tw1_1_4_2_calc_x j
    · exact tw1_1_4_3_calc_x j
    · exact tw1_1_4_4_calc_x j
    · exact tw1_1_4_5_calc_x j
    · exact tw1_1_4_6_calc_x j
    · exact tw1_1_4_7_calc_x j
    · exact tw1_1_4_8_calc_x j
    · exact tw1_1_4_9_calc_x j
    · exact tw1_1_4_10_calc_x j
    · exact tw1_1_4_11_calc_x j
    · exact tw1_1_4_12_calc_x j
    · exact tw1_1_4_13_calc_x j
    · exact tw1_1_4_14_calc_x j
    · exact tw1_1_4_15_calc_x j
    · exact tw1_1_4_16_calc j
    · exact tw1_1_4_17_calc j
    · exact tw1_1_4_18_calc j
    · exact tw1_1_4_19_calc j
    · exact tw1_1_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 1 1 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_x_oai
