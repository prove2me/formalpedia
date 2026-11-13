-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:48:27.340222+00:00
-- url     : https://prove2.me/submissions/7eba02b7-40c2-458d-8f5d-a9c096c75a52

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_15_calc (j : Fin 31) : taylorWaveBox 1 0 3 15 j = tw1_0_3_15 j := by
  revert j
  decide +kernel
lemma tw1_0_3_16_calc (j : Fin 31) : taylorWaveBox 1 0 3 16 j = tw1_0_3_16 j := by
  revert j
  decide +kernel
lemma tw1_0_3_17_calc (j : Fin 31) : taylorWaveBox 1 0 3 17 j = tw1_0_3_17 j := by
  revert j
  decide +kernel
lemma tw1_0_3_18_calc (j : Fin 31) : taylorWaveBox 1 0 3 18 j = tw1_0_3_18 j := by
  revert j
  decide +kernel
lemma tw1_0_3_19_calc (j : Fin 31) : taylorWaveBox 1 0 3 19 j = tw1_0_3_19 j := by
  revert j
  decide +kernel
lemma tw1_0_3_20_calc (j : Fin 31) : taylorWaveBox 1 0 3 20 j = tw1_0_3_20 j := by
  revert j
  decide +kernel
lemma tw1_0_3_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw1_0_3 l j).Mem (taylorWave 1 0 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 3 l j = tw1_0_3 l j := by
    fin_cases l
    · exact tw1_0_3_0_calc_x j
    · exact tw1_0_3_1_calc_x j
    · exact tw1_0_3_2_calc_x j
    · exact tw1_0_3_3_calc_x j
    · exact tw1_0_3_4_calc_x j
    · exact tw1_0_3_5_calc_x j
    · exact tw1_0_3_6_calc_x j
    · exact tw1_0_3_7_calc_x j
    · exact tw1_0_3_8_calc_x j
    · exact tw1_0_3_9_calc_x j
    · exact tw1_0_3_10_calc_x j
    · exact tw1_0_3_11_calc_x j
    · exact tw1_0_3_12_calc_x j
    · exact tw1_0_3_13_calc_x j
    · exact tw1_0_3_14_calc_x j
    · exact tw1_0_3_15_calc j
    · exact tw1_0_3_16_calc j
    · exact tw1_0_3_17_calc j
    · exact tw1_0_3_18_calc j
    · exact tw1_0_3_19_calc j
    · exact tw1_0_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 1 0 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_x_oai
