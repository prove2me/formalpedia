-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:09:41.930578+00:00
-- url     : https://prove2.me/submissions/29784962-f068-4634-9558-e75ba5094d43

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_8_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_9_calc (j : Fin 31) : taylorWaveBox 1 0 3 9 j = tw1_0_3_9 j := by
  revert j
  decide +kernel
lemma tw1_0_3_17_calc (j : Fin 31) : taylorWaveBox 1 0 3 17 j = tw1_0_3_17 j := by
  revert j
  decide +kernel
lemma tw1_0_3_18_calc (j : Fin 31) : taylorWaveBox 1 0 3 18 j = tw1_0_3_18 j := by
  revert j
  decide +kernel
lemma tw1_0_3_19_calc (j : Fin 31) : taylorWaveBox 1 0 3 19 j = tw1_0_3_19 j := by
  revert j
  decide +kernel
lemma tw1_0_3_20_calc (j : Fin 31) : taylorWaveBox 1 0 3 20 j = tw1_0_3_20 j := by
  revert j
  decide +kernel
lemma tw1_0_3_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw1_0_3 l j).Mem (taylorWave 1 0 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 3 l j = tw1_0_3 l j := by
    fin_cases l
    · exact tw1_0_3_0_calc_eu j
    · exact tw1_0_3_1_calc_eu j
    · exact tw1_0_3_2_calc_eu j
    · exact tw1_0_3_3_calc_eu j
    · exact tw1_0_3_4_calc_eu j
    · exact tw1_0_3_5_calc_eu j
    · exact tw1_0_3_6_calc_eu j
    · exact tw1_0_3_7_calc_eu j
    · exact tw1_0_3_8_calc_eu j
    · exact tw1_0_3_9_calc j
    · exact tw1_0_3_10_calc_eu j
    · exact tw1_0_3_11_calc_eu j
    · exact tw1_0_3_12_calc_eu j
    · exact tw1_0_3_13_calc_eu j
    · exact tw1_0_3_14_calc_eu j
    · exact tw1_0_3_15_calc_eu j
    · exact tw1_0_3_16_calc_eu j
    · exact tw1_0_3_17_calc j
    · exact tw1_0_3_18_calc j
    · exact tw1_0_3_19_calc j
    · exact tw1_0_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 1 0 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_eu_oai
