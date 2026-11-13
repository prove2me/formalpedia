-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:45:04.652462+00:00
-- url     : https://prove2.me/submissions/c1369cbd-1f39-48ef-acd2-addde338fc7b

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_1_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_1_10_calc (j : Fin 31) : taylorWaveBox 1 0 1 10 j = tw1_0_1_10 j := by
  revert j
  decide +kernel
lemma tw1_0_1_11_calc (j : Fin 31) : taylorWaveBox 1 0 1 11 j = tw1_0_1_11 j := by
  revert j
  decide +kernel
lemma tw1_0_1_17_calc (j : Fin 31) : taylorWaveBox 1 0 1 17 j = tw1_0_1_17 j := by
  revert j
  decide +kernel
lemma tw1_0_1_18_calc (j : Fin 31) : taylorWaveBox 1 0 1 18 j = tw1_0_1_18 j := by
  revert j
  decide +kernel
lemma tw1_0_1_19_calc (j : Fin 31) : taylorWaveBox 1 0 1 19 j = tw1_0_1_19 j := by
  revert j
  decide +kernel
lemma tw1_0_1_20_calc (j : Fin 31) : taylorWaveBox 1 0 1 20 j = tw1_0_1_20 j := by
  revert j
  decide +kernel
lemma tw1_0_1_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw1_0_1 l j).Mem (taylorWave 1 0 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 1 l j = tw1_0_1 l j := by
    fin_cases l
    · exact tw1_0_1_0_calc_x j
    · exact tw1_0_1_1_calc_x j
    · exact tw1_0_1_2_calc_x j
    · exact tw1_0_1_3_calc_x j
    · exact tw1_0_1_4_calc_x j
    · exact tw1_0_1_5_calc_x j
    · exact tw1_0_1_6_calc_x j
    · exact tw1_0_1_7_calc_x j
    · exact tw1_0_1_8_calc_x j
    · exact tw1_0_1_9_calc_x j
    · exact tw1_0_1_10_calc j
    · exact tw1_0_1_11_calc j
    · exact tw1_0_1_12_calc_x j
    · exact tw1_0_1_13_calc_x j
    · exact tw1_0_1_14_calc_x j
    · exact tw1_0_1_15_calc_x j
    · exact tw1_0_1_16_calc_x j
    · exact tw1_0_1_17_calc j
    · exact tw1_0_1_18_calc j
    · exact tw1_0_1_19_calc j
    · exact tw1_0_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 1 0 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_x_oai
