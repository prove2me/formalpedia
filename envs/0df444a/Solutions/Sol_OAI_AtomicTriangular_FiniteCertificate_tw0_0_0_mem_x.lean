-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:19:44.143893+00:00
-- url     : https://prove2.me/submissions/1176d94a-ca4d-4a1f-b116-a387ce7b5e06

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_0_calc (j : Fin 31) : taylorWaveBox 0 0 0 0 j = tw0_0_0_0 j := by
  revert j
  decide +kernel
lemma tw0_0_0_10_calc (j : Fin 31) : taylorWaveBox 0 0 0 10 j = tw0_0_0_10 j := by
  revert j
  decide +kernel
lemma tw0_0_0_16_calc (j : Fin 31) : taylorWaveBox 0 0 0 16 j = tw0_0_0_16 j := by
  revert j
  decide +kernel
lemma tw0_0_0_17_calc (j : Fin 31) : taylorWaveBox 0 0 0 17 j = tw0_0_0_17 j := by
  revert j
  decide +kernel
lemma tw0_0_0_18_calc (j : Fin 31) : taylorWaveBox 0 0 0 18 j = tw0_0_0_18 j := by
  revert j
  decide +kernel
lemma tw0_0_0_19_calc (j : Fin 31) : taylorWaveBox 0 0 0 19 j = tw0_0_0_19 j := by
  revert j
  decide +kernel
lemma tw0_0_0_20_calc (j : Fin 31) : taylorWaveBox 0 0 0 20 j = tw0_0_0_20 j := by
  revert j
  decide +kernel
lemma tw0_0_0_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw0_0_0 l j).Mem (taylorWave 0 0 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 0 l j = tw0_0_0 l j := by
    fin_cases l
    · exact tw0_0_0_0_calc j
    · exact tw0_0_0_1_calc_x j
    · exact tw0_0_0_2_calc_x j
    · exact tw0_0_0_3_calc_x j
    · exact tw0_0_0_4_calc_x j
    · exact tw0_0_0_5_calc_x j
    · exact tw0_0_0_6_calc_x j
    · exact tw0_0_0_7_calc_x j
    · exact tw0_0_0_8_calc_x j
    · exact tw0_0_0_9_calc_x j
    · exact tw0_0_0_10_calc j
    · exact tw0_0_0_11_calc_x j
    · exact tw0_0_0_12_calc_x j
    · exact tw0_0_0_13_calc_x j
    · exact tw0_0_0_14_calc_x j
    · exact tw0_0_0_15_calc_x j
    · exact tw0_0_0_16_calc j
    · exact tw0_0_0_17_calc j
    · exact tw0_0_0_18_calc j
    · exact tw0_0_0_19_calc j
    · exact tw0_0_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 0 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_x_oai
