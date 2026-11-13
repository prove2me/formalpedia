-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:04:15.021076+00:00
-- url     : https://prove2.me/submissions/def933af-c16e-4b87-a4e7-c615b40e6b16

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_5_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_6_0_calc (j : Fin 31) : taylorWaveBox 1 1 6 0 j = tw1_1_6_0 j := by
  revert j
  decide +kernel
lemma tw1_1_6_16_calc (j : Fin 31) : taylorWaveBox 1 1 6 16 j = tw1_1_6_16 j := by
  revert j
  decide +kernel
lemma tw1_1_6_17_calc (j : Fin 31) : taylorWaveBox 1 1 6 17 j = tw1_1_6_17 j := by
  revert j
  decide +kernel
lemma tw1_1_6_18_calc (j : Fin 31) : taylorWaveBox 1 1 6 18 j = tw1_1_6_18 j := by
  revert j
  decide +kernel
lemma tw1_1_6_19_calc (j : Fin 31) : taylorWaveBox 1 1 6 19 j = tw1_1_6_19 j := by
  revert j
  decide +kernel
lemma tw1_1_6_20_calc (j : Fin 31) : taylorWaveBox 1 1 6 20 j = tw1_1_6_20 j := by
  revert j
  decide +kernel
lemma tw1_1_6_mem (l : Fin 21) (j : Fin 31) : (tw1_1_6 l j).Mem (taylorWave 1 1 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 6 l j = tw1_1_6 l j := by
    fin_cases l
    · exact tw1_1_6_0_calc j
    · exact tw1_1_6_1_calc_x j
    · exact tw1_1_6_2_calc_x j
    · exact tw1_1_6_3_calc_x j
    · exact tw1_1_6_4_calc_x j
    · exact tw1_1_6_5_calc_x j
    · exact tw1_1_6_6_calc_x j
    · exact tw1_1_6_7_calc_x j
    · exact tw1_1_6_8_calc_x j
    · exact tw1_1_6_9_calc_x j
    · exact tw1_1_6_10_calc_x j
    · exact tw1_1_6_11_calc_x j
    · exact tw1_1_6_12_calc_x j
    · exact tw1_1_6_13_calc_x j
    · exact tw1_1_6_14_calc_x j
    · exact tw1_1_6_15_calc_x j
    · exact tw1_1_6_16_calc j
    · exact tw1_1_6_17_calc j
    · exact tw1_1_6_18_calc j
    · exact tw1_1_6_19_calc j
    · exact tw1_1_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 1 1 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_mem_x_oai (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_1 n l j).Mem (taylorWave 1 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_1_0_mem_x l j
  · exact tw1_1_1_mem_x l j
  · exact tw1_1_2_mem_x l j
  · exact tw1_1_3_mem_x l j
  · exact tw1_1_4_mem_x l j
  · exact tw1_1_5_mem_x l j
  · exact tw1_1_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_x_oai
