-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:04:12.210212+00:00
-- url     : https://prove2.me/submissions/48401437-2f6a-4b20-a182-7dc8a064c9a5

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_6_16_calc (j : Fin 31) : taylorWaveBox 0 1 6 16 j = tw0_1_6_16 j := by
  revert j
  decide +kernel
lemma tw0_1_6_17_calc (j : Fin 31) : taylorWaveBox 0 1 6 17 j = tw0_1_6_17 j := by
  revert j
  decide +kernel
lemma tw0_1_6_18_calc (j : Fin 31) : taylorWaveBox 0 1 6 18 j = tw0_1_6_18 j := by
  revert j
  decide +kernel
lemma tw0_1_6_19_calc (j : Fin 31) : taylorWaveBox 0 1 6 19 j = tw0_1_6_19 j := by
  revert j
  decide +kernel
lemma tw0_1_6_20_calc (j : Fin 31) : taylorWaveBox 0 1 6 20 j = tw0_1_6_20 j := by
  revert j
  decide +kernel
lemma tw0_1_6_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_1_6 l j).Mem (taylorWave 0 1 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 6 l j = tw0_1_6 l j := by
    fin_cases l
    · exact tw0_1_6_0_calc_eu j
    · exact tw0_1_6_1_calc_eu j
    · exact tw0_1_6_2_calc_eu j
    · exact tw0_1_6_3_calc_eu j
    · exact tw0_1_6_4_calc_eu j
    · exact tw0_1_6_5_calc_eu j
    · exact tw0_1_6_6_calc_eu j
    · exact tw0_1_6_7_calc_eu j
    · exact tw0_1_6_8_calc_eu j
    · exact tw0_1_6_9_calc_eu j
    · exact tw0_1_6_10_calc_eu j
    · exact tw0_1_6_11_calc_eu j
    · exact tw0_1_6_12_calc_eu j
    · exact tw0_1_6_13_calc_eu j
    · exact tw0_1_6_14_calc_eu j
    · exact tw0_1_6_15_calc_eu j
    · exact tw0_1_6_16_calc j
    · exact tw0_1_6_17_calc j
    · exact tw0_1_6_18_calc j
    · exact tw0_1_6_19_calc j
    · exact tw0_1_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 1 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_eu_oai
