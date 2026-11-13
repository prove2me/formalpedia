-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:58:22.275537+00:00
-- url     : https://prove2.me/submissions/cb100a20-1568-425f-bcdc-a1ec3e855a66

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_19_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_20_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_4_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_2_3_calc (j : Fin 31) : taylorWaveBox 1 1 2 3 j = tw1_1_2_3 j := by
  revert j
  decide +kernel
lemma tw1_1_2_5_calc (j : Fin 31) : taylorWaveBox 1 1 2 5 j = tw1_1_2_5 j := by
  revert j
  decide +kernel
lemma tw1_1_2_6_calc (j : Fin 31) : taylorWaveBox 1 1 2 6 j = tw1_1_2_6 j := by
  revert j
  decide +kernel
lemma tw1_1_2_7_calc (j : Fin 31) : taylorWaveBox 1 1 2 7 j = tw1_1_2_7 j := by
  revert j
  decide +kernel
lemma tw1_1_2_8_calc (j : Fin 31) : taylorWaveBox 1 1 2 8 j = tw1_1_2_8 j := by
  revert j
  decide +kernel
lemma tw1_1_2_9_calc (j : Fin 31) : taylorWaveBox 1 1 2 9 j = tw1_1_2_9 j := by
  revert j
  decide +kernel
lemma tw1_1_2_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw1_1_2 l j).Mem (taylorWave 1 1 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 2 l j = tw1_1_2 l j := by
    fin_cases l
    · exact tw1_1_2_0_calc_x j
    · exact tw1_1_2_1_calc_x j
    · exact tw1_1_2_2_calc_x j
    · exact tw1_1_2_3_calc j
    · exact tw1_1_2_4_calc_x j
    · exact tw1_1_2_5_calc j
    · exact tw1_1_2_6_calc j
    · exact tw1_1_2_7_calc j
    · exact tw1_1_2_8_calc j
    · exact tw1_1_2_9_calc j
    · exact tw1_1_2_10_calc_x j
    · exact tw1_1_2_11_calc_x j
    · exact tw1_1_2_12_calc_x j
    · exact tw1_1_2_13_calc_x j
    · exact tw1_1_2_14_calc_x j
    · exact tw1_1_2_15_calc_x j
    · exact tw1_1_2_16_calc_x j
    · exact tw1_1_2_17_calc_x j
    · exact tw1_1_2_18_calc_x j
    · exact tw1_1_2_19_calc_x j
    · exact tw1_1_2_20_calc_x j
  rw [← he]
  exact taylorWaveBox_mem_x 1 1 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_x_oai
