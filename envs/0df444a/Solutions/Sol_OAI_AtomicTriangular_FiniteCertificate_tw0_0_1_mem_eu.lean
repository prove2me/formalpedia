-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:54:23.573588+00:00
-- url     : https://prove2.me/submissions/e11c435b-a030-4fd1-b0d2-bdc9ae90ad15

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_19_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_1_10_calc (j : Fin 31) : taylorWaveBox 0 0 1 10 j = tw0_0_1_10 j := by
  revert j
  decide +kernel
lemma tw0_0_1_11_calc (j : Fin 31) : taylorWaveBox 0 0 1 11 j = tw0_0_1_11 j := by
  revert j
  decide +kernel
lemma tw0_0_1_12_calc (j : Fin 31) : taylorWaveBox 0 0 1 12 j = tw0_0_1_12 j := by
  revert j
  decide +kernel
lemma tw0_0_1_13_calc (j : Fin 31) : taylorWaveBox 0 0 1 13 j = tw0_0_1_13 j := by
  revert j
  decide +kernel
lemma tw0_0_1_14_calc (j : Fin 31) : taylorWaveBox 0 0 1 14 j = tw0_0_1_14 j := by
  revert j
  decide +kernel
lemma tw0_0_1_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_0_1 l j).Mem (taylorWave 0 0 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 1 l j = tw0_0_1 l j := by
    fin_cases l
    · exact tw0_0_1_0_calc_eu j
    · exact tw0_0_1_1_calc_eu j
    · exact tw0_0_1_2_calc_eu j
    · exact tw0_0_1_3_calc_eu j
    · exact tw0_0_1_4_calc_eu j
    · exact tw0_0_1_5_calc_eu j
    · exact tw0_0_1_6_calc_eu j
    · exact tw0_0_1_7_calc_eu j
    · exact tw0_0_1_8_calc_eu j
    · exact tw0_0_1_9_calc_eu j
    · exact tw0_0_1_10_calc j
    · exact tw0_0_1_11_calc j
    · exact tw0_0_1_12_calc j
    · exact tw0_0_1_13_calc j
    · exact tw0_0_1_14_calc j
    · exact tw0_0_1_15_calc_eu j
    · exact tw0_0_1_16_calc_eu j
    · exact tw0_0_1_17_calc_eu j
    · exact tw0_0_1_18_calc_eu j
    · exact tw0_0_1_19_calc_eu j
    · exact tw0_0_1_20_calc_eu j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 0 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_eu_oai
