-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:29:42.100203+00:00
-- url     : https://prove2.me/submissions/f9075eff-a882-4d5f-9d93-37d30ae35396

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_0_16_calc (j : Fin 31) : taylorWaveBox 0 1 0 16 j = tw0_1_0_16 j := by
  revert j
  decide +kernel
lemma tw0_1_0_17_calc (j : Fin 31) : taylorWaveBox 0 1 0 17 j = tw0_1_0_17 j := by
  revert j
  decide +kernel
lemma tw0_1_0_18_calc (j : Fin 31) : taylorWaveBox 0 1 0 18 j = tw0_1_0_18 j := by
  revert j
  decide +kernel
lemma tw0_1_0_19_calc (j : Fin 31) : taylorWaveBox 0 1 0 19 j = tw0_1_0_19 j := by
  revert j
  decide +kernel
lemma tw0_1_0_20_calc (j : Fin 31) : taylorWaveBox 0 1 0 20 j = tw0_1_0_20 j := by
  revert j
  decide +kernel
lemma tw0_1_0_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw0_1_0 l j).Mem (taylorWave 0 1 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 0 l j = tw0_1_0 l j := by
    fin_cases l
    · exact tw0_1_0_0_calc_x j
    · exact tw0_1_0_1_calc_x j
    · exact tw0_1_0_2_calc_x j
    · exact tw0_1_0_3_calc_x j
    · exact tw0_1_0_4_calc_x j
    · exact tw0_1_0_5_calc_x j
    · exact tw0_1_0_6_calc_x j
    · exact tw0_1_0_7_calc_x j
    · exact tw0_1_0_8_calc_x j
    · exact tw0_1_0_9_calc_x j
    · exact tw0_1_0_10_calc_x j
    · exact tw0_1_0_11_calc_x j
    · exact tw0_1_0_12_calc_x j
    · exact tw0_1_0_13_calc_x j
    · exact tw0_1_0_14_calc_x j
    · exact tw0_1_0_15_calc_x j
    · exact tw0_1_0_16_calc j
    · exact tw0_1_0_17_calc j
    · exact tw0_1_0_18_calc j
    · exact tw0_1_0_19_calc j
    · exact tw0_1_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 1 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_x_oai
