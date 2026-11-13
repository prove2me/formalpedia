-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:37:54.719413+00:00
-- url     : https://prove2.me/submissions/e0e8accf-111f-4b48-8e14-30560d9cc66e

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_5_16_calc (j : Fin 31) : taylorWaveBox 0 1 5 16 j = tw0_1_5_16 j := by
  revert j
  decide +kernel
lemma tw0_1_5_17_calc (j : Fin 31) : taylorWaveBox 0 1 5 17 j = tw0_1_5_17 j := by
  revert j
  decide +kernel
lemma tw0_1_5_18_calc (j : Fin 31) : taylorWaveBox 0 1 5 18 j = tw0_1_5_18 j := by
  revert j
  decide +kernel
lemma tw0_1_5_19_calc (j : Fin 31) : taylorWaveBox 0 1 5 19 j = tw0_1_5_19 j := by
  revert j
  decide +kernel
lemma tw0_1_5_20_calc (j : Fin 31) : taylorWaveBox 0 1 5 20 j = tw0_1_5_20 j := by
  revert j
  decide +kernel
lemma tw0_1_5_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw0_1_5 l j).Mem (taylorWave 0 1 (nearNode 5) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 5 l j = tw0_1_5 l j := by
    fin_cases l
    · exact tw0_1_5_0_calc_x j
    · exact tw0_1_5_1_calc_x j
    · exact tw0_1_5_2_calc_x j
    · exact tw0_1_5_3_calc_x j
    · exact tw0_1_5_4_calc_x j
    · exact tw0_1_5_5_calc_x j
    · exact tw0_1_5_6_calc_x j
    · exact tw0_1_5_7_calc_x j
    · exact tw0_1_5_8_calc_x j
    · exact tw0_1_5_9_calc_x j
    · exact tw0_1_5_10_calc_x j
    · exact tw0_1_5_11_calc_x j
    · exact tw0_1_5_12_calc_x j
    · exact tw0_1_5_13_calc_x j
    · exact tw0_1_5_14_calc_x j
    · exact tw0_1_5_15_calc_x j
    · exact tw0_1_5_16_calc j
    · exact tw0_1_5_17_calc j
    · exact tw0_1_5_18_calc j
    · exact tw0_1_5_19_calc j
    · exact tw0_1_5_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 1 5 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_x_oai
