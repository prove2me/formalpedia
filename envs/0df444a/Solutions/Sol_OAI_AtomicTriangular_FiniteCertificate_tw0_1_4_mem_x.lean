-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:36:17.560565+00:00
-- url     : https://prove2.me/submissions/89688ac4-a93e-42b1-973f-7385976454c7

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_1_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_4_2_calc (j : Fin 31) : taylorWaveBox 0 1 4 2 j = tw0_1_4_2 j := by
  revert j
  decide +kernel
lemma tw0_1_4_3_calc (j : Fin 31) : taylorWaveBox 0 1 4 3 j = tw0_1_4_3 j := by
  revert j
  decide +kernel
lemma tw0_1_4_4_calc (j : Fin 31) : taylorWaveBox 0 1 4 4 j = tw0_1_4_4 j := by
  revert j
  decide +kernel
lemma tw0_1_4_5_calc (j : Fin 31) : taylorWaveBox 0 1 4 5 j = tw0_1_4_5 j := by
  revert j
  decide +kernel
lemma tw0_1_4_6_calc (j : Fin 31) : taylorWaveBox 0 1 4 6 j = tw0_1_4_6 j := by
  revert j
  decide +kernel
lemma tw0_1_4_7_calc (j : Fin 31) : taylorWaveBox 0 1 4 7 j = tw0_1_4_7 j := by
  revert j
  decide +kernel
lemma tw0_1_4_8_calc (j : Fin 31) : taylorWaveBox 0 1 4 8 j = tw0_1_4_8 j := by
  revert j
  decide +kernel
lemma tw0_1_4_9_calc (j : Fin 31) : taylorWaveBox 0 1 4 9 j = tw0_1_4_9 j := by
  revert j
  decide +kernel
lemma tw0_1_4_18_calc (j : Fin 31) : taylorWaveBox 0 1 4 18 j = tw0_1_4_18 j := by
  revert j
  decide +kernel
lemma tw0_1_4_19_calc (j : Fin 31) : taylorWaveBox 0 1 4 19 j = tw0_1_4_19 j := by
  revert j
  decide +kernel
lemma tw0_1_4_20_calc (j : Fin 31) : taylorWaveBox 0 1 4 20 j = tw0_1_4_20 j := by
  revert j
  decide +kernel
lemma tw0_1_4_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw0_1_4 l j).Mem (taylorWave 0 1 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 4 l j = tw0_1_4 l j := by
    fin_cases l
    · exact tw0_1_4_0_calc_x j
    · exact tw0_1_4_1_calc_x j
    · exact tw0_1_4_2_calc j
    · exact tw0_1_4_3_calc j
    · exact tw0_1_4_4_calc j
    · exact tw0_1_4_5_calc j
    · exact tw0_1_4_6_calc j
    · exact tw0_1_4_7_calc j
    · exact tw0_1_4_8_calc j
    · exact tw0_1_4_9_calc j
    · exact tw0_1_4_10_calc_x j
    · exact tw0_1_4_11_calc_x j
    · exact tw0_1_4_12_calc_x j
    · exact tw0_1_4_13_calc_x j
    · exact tw0_1_4_14_calc_x j
    · exact tw0_1_4_15_calc_x j
    · exact tw0_1_4_16_calc_x j
    · exact tw0_1_4_17_calc_x j
    · exact tw0_1_4_18_calc j
    · exact tw0_1_4_19_calc j
    · exact tw0_1_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 1 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_x_oai
