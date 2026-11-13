-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:24:05.478293+00:00
-- url     : https://prove2.me/submissions/47d5ab91-0c40-43cc-b320-e0544b881ba4

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_1_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_2_2_calc (j : Fin 31) : taylorWaveBox 0 0 2 2 j = tw0_0_2_2 j := by
  revert j
  decide +kernel
lemma tw0_0_2_3_calc (j : Fin 31) : taylorWaveBox 0 0 2 3 j = tw0_0_2_3 j := by
  revert j
  decide +kernel
lemma tw0_0_2_4_calc (j : Fin 31) : taylorWaveBox 0 0 2 4 j = tw0_0_2_4 j := by
  revert j
  decide +kernel
lemma tw0_0_2_5_calc (j : Fin 31) : taylorWaveBox 0 0 2 5 j = tw0_0_2_5 j := by
  revert j
  decide +kernel
lemma tw0_0_2_6_calc (j : Fin 31) : taylorWaveBox 0 0 2 6 j = tw0_0_2_6 j := by
  revert j
  decide +kernel
lemma tw0_0_2_7_calc (j : Fin 31) : taylorWaveBox 0 0 2 7 j = tw0_0_2_7 j := by
  revert j
  decide +kernel
lemma tw0_0_2_8_calc (j : Fin 31) : taylorWaveBox 0 0 2 8 j = tw0_0_2_8 j := by
  revert j
  decide +kernel
lemma tw0_0_2_9_calc (j : Fin 31) : taylorWaveBox 0 0 2 9 j = tw0_0_2_9 j := by
  revert j
  decide +kernel
lemma tw0_0_2_18_calc (j : Fin 31) : taylorWaveBox 0 0 2 18 j = tw0_0_2_18 j := by
  revert j
  decide +kernel
lemma tw0_0_2_19_calc (j : Fin 31) : taylorWaveBox 0 0 2 19 j = tw0_0_2_19 j := by
  revert j
  decide +kernel
lemma tw0_0_2_20_calc (j : Fin 31) : taylorWaveBox 0 0 2 20 j = tw0_0_2_20 j := by
  revert j
  decide +kernel
lemma tw0_0_2_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_0_2 l j).Mem (taylorWave 0 0 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 2 l j = tw0_0_2 l j := by
    fin_cases l
    · exact tw0_0_2_0_calc_eu j
    · exact tw0_0_2_1_calc_eu j
    · exact tw0_0_2_2_calc j
    · exact tw0_0_2_3_calc j
    · exact tw0_0_2_4_calc j
    · exact tw0_0_2_5_calc j
    · exact tw0_0_2_6_calc j
    · exact tw0_0_2_7_calc j
    · exact tw0_0_2_8_calc j
    · exact tw0_0_2_9_calc j
    · exact tw0_0_2_10_calc_eu j
    · exact tw0_0_2_11_calc_eu j
    · exact tw0_0_2_12_calc_eu j
    · exact tw0_0_2_13_calc_eu j
    · exact tw0_0_2_14_calc_eu j
    · exact tw0_0_2_15_calc_eu j
    · exact tw0_0_2_16_calc_eu j
    · exact tw0_0_2_17_calc_eu j
    · exact tw0_0_2_18_calc j
    · exact tw0_0_2_19_calc j
    · exact tw0_0_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 0 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_eu_oai
