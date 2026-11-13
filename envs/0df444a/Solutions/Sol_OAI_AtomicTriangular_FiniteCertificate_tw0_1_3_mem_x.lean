-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:35:12.764959+00:00
-- url     : https://prove2.me/submissions/b53b1710-02e8-401a-8e7e-4a13c077486b

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_3_0_calc (j : Fin 31) : taylorWaveBox 0 1 3 0 j = tw0_1_3_0 j := by
  revert j
  decide +kernel
lemma tw0_1_3_12_calc (j : Fin 31) : taylorWaveBox 0 1 3 12 j = tw0_1_3_12 j := by
  revert j
  decide +kernel
lemma tw0_1_3_18_calc (j : Fin 31) : taylorWaveBox 0 1 3 18 j = tw0_1_3_18 j := by
  revert j
  decide +kernel
lemma tw0_1_3_19_calc (j : Fin 31) : taylorWaveBox 0 1 3 19 j = tw0_1_3_19 j := by
  revert j
  decide +kernel
lemma tw0_1_3_20_calc (j : Fin 31) : taylorWaveBox 0 1 3 20 j = tw0_1_3_20 j := by
  revert j
  decide +kernel
lemma tw0_1_3_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw0_1_3 l j).Mem (taylorWave 0 1 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 3 l j = tw0_1_3 l j := by
    fin_cases l
    · exact tw0_1_3_0_calc j
    · exact tw0_1_3_1_calc_x j
    · exact tw0_1_3_2_calc_x j
    · exact tw0_1_3_3_calc_x j
    · exact tw0_1_3_4_calc_x j
    · exact tw0_1_3_5_calc_x j
    · exact tw0_1_3_6_calc_x j
    · exact tw0_1_3_7_calc_x j
    · exact tw0_1_3_8_calc_x j
    · exact tw0_1_3_9_calc_x j
    · exact tw0_1_3_10_calc_x j
    · exact tw0_1_3_11_calc_x j
    · exact tw0_1_3_12_calc j
    · exact tw0_1_3_13_calc_x j
    · exact tw0_1_3_14_calc_x j
    · exact tw0_1_3_15_calc_x j
    · exact tw0_1_3_16_calc_x j
    · exact tw0_1_3_17_calc_x j
    · exact tw0_1_3_18_calc j
    · exact tw0_1_3_19_calc j
    · exact tw0_1_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 1 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_x_oai
