-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:28:17.55793+00:00
-- url     : https://prove2.me/submissions/a3c5589c-5f4c-4bb0-8c2e-1eb2f4e4cd03

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_2_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_0_3_calc (j : Fin 31) : taylorWaveBox 0 1 0 3 j = tw0_1_0_3 j := by
  revert j
  decide +kernel
lemma tw0_1_0_4_calc (j : Fin 31) : taylorWaveBox 0 1 0 4 j = tw0_1_0_4 j := by
  revert j
  decide +kernel
lemma tw0_1_0_5_calc (j : Fin 31) : taylorWaveBox 0 1 0 5 j = tw0_1_0_5 j := by
  revert j
  decide +kernel
lemma tw0_1_0_6_calc (j : Fin 31) : taylorWaveBox 0 1 0 6 j = tw0_1_0_6 j := by
  revert j
  decide +kernel
lemma tw0_1_0_7_calc (j : Fin 31) : taylorWaveBox 0 1 0 7 j = tw0_1_0_7 j := by
  revert j
  decide +kernel
lemma tw0_1_0_8_calc (j : Fin 31) : taylorWaveBox 0 1 0 8 j = tw0_1_0_8 j := by
  revert j
  decide +kernel
lemma tw0_1_0_9_calc (j : Fin 31) : taylorWaveBox 0 1 0 9 j = tw0_1_0_9 j := by
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
lemma tw0_1_0_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_1_0 l j).Mem (taylorWave 0 1 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 0 l j = tw0_1_0 l j := by
    fin_cases l
    · exact tw0_1_0_0_calc_eu j
    · exact tw0_1_0_1_calc_eu j
    · exact tw0_1_0_2_calc_eu j
    · exact tw0_1_0_3_calc j
    · exact tw0_1_0_4_calc j
    · exact tw0_1_0_5_calc j
    · exact tw0_1_0_6_calc j
    · exact tw0_1_0_7_calc j
    · exact tw0_1_0_8_calc j
    · exact tw0_1_0_9_calc j
    · exact tw0_1_0_10_calc_eu j
    · exact tw0_1_0_11_calc_eu j
    · exact tw0_1_0_12_calc_eu j
    · exact tw0_1_0_13_calc_eu j
    · exact tw0_1_0_14_calc_eu j
    · exact tw0_1_0_15_calc_eu j
    · exact tw0_1_0_16_calc_eu j
    · exact tw0_1_0_17_calc_eu j
    · exact tw0_1_0_18_calc j
    · exact tw0_1_0_19_calc j
    · exact tw0_1_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 1 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_eu_oai
