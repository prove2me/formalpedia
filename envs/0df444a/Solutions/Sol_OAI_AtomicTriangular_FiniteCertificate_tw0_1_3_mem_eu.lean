-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:59:13.09821+00:00
-- url     : https://prove2.me/submissions/5280ed0f-1200-4780-8b70-d55fb58b65fd

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave013
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
lemma tw0_1_3_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_1_3 l j).Mem (taylorWave 0 1 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 3 l j = tw0_1_3 l j := by
    fin_cases l
    · exact tw0_1_3_0_calc j
    · exact tw0_1_3_1_calc_eu j
    · exact tw0_1_3_2_calc_eu j
    · exact tw0_1_3_3_calc_eu j
    · exact tw0_1_3_4_calc_eu j
    · exact tw0_1_3_5_calc_eu j
    · exact tw0_1_3_6_calc_eu j
    · exact tw0_1_3_7_calc_eu j
    · exact tw0_1_3_8_calc_eu j
    · exact tw0_1_3_9_calc_eu j
    · exact tw0_1_3_10_calc_eu j
    · exact tw0_1_3_11_calc_eu j
    · exact tw0_1_3_12_calc j
    · exact tw0_1_3_13_calc_eu j
    · exact tw0_1_3_14_calc_eu j
    · exact tw0_1_3_15_calc_eu j
    · exact tw0_1_3_16_calc_eu j
    · exact tw0_1_3_17_calc_eu j
    · exact tw0_1_3_18_calc j
    · exact tw0_1_3_19_calc j
    · exact tw0_1_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 1 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_eu_oai
