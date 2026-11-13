-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:31:44.117907+00:00
-- url     : https://prove2.me/submissions/819da96f-d271-4821-9949-cfc283d2070e

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_9_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_1_16_calc (j : Fin 31) : taylorWaveBox 0 1 1 16 j = tw0_1_1_16 j := by
  revert j
  decide +kernel
lemma tw0_1_1_17_calc (j : Fin 31) : taylorWaveBox 0 1 1 17 j = tw0_1_1_17 j := by
  revert j
  decide +kernel
lemma tw0_1_1_18_calc (j : Fin 31) : taylorWaveBox 0 1 1 18 j = tw0_1_1_18 j := by
  revert j
  decide +kernel
lemma tw0_1_1_19_calc (j : Fin 31) : taylorWaveBox 0 1 1 19 j = tw0_1_1_19 j := by
  revert j
  decide +kernel
lemma tw0_1_1_20_calc (j : Fin 31) : taylorWaveBox 0 1 1 20 j = tw0_1_1_20 j := by
  revert j
  decide +kernel
lemma tw0_1_1_mem (l : Fin 21) (j : Fin 31) : (tw0_1_1 l j).Mem (taylorWave 0 1 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 1 l j = tw0_1_1 l j := by
    fin_cases l
    · exact tw0_1_1_0_calc_x j
    · exact tw0_1_1_1_calc_x j
    · exact tw0_1_1_2_calc_x j
    · exact tw0_1_1_3_calc_x j
    · exact tw0_1_1_4_calc_x j
    · exact tw0_1_1_5_calc_x j
    · exact tw0_1_1_6_calc_x j
    · exact tw0_1_1_7_calc_x j
    · exact tw0_1_1_8_calc_x j
    · exact tw0_1_1_9_calc_x j
    · exact tw0_1_1_10_calc_x j
    · exact tw0_1_1_11_calc_x j
    · exact tw0_1_1_12_calc_x j
    · exact tw0_1_1_13_calc_x j
    · exact tw0_1_1_14_calc_x j
    · exact tw0_1_1_15_calc_x j
    · exact tw0_1_1_16_calc j
    · exact tw0_1_1_17_calc j
    · exact tw0_1_1_18_calc j
    · exact tw0_1_1_19_calc j
    · exact tw0_1_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 1 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_mem_x_oai (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_1 n l j).Mem (taylorWave 0 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_1_0_mem_x l j
  · exact tw0_1_1_mem l j
  · exact tw0_1_2_mem_x l j
  · exact tw0_1_3_mem_x l j
  · exact tw0_1_4_mem_x l j
  · exact tw0_1_5_mem_x l j
  · exact tw0_1_6_mem_x l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_x_oai
