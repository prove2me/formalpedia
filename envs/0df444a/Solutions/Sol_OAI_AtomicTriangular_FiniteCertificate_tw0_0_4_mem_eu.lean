-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:54:56.122695+00:00
-- url     : https://prove2.me/submissions/32336879-f45b-4791-8cc7-120fc0c8d818

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_4_10_calc (j : Fin 31) : taylorWaveBox 0 0 4 10 j = tw0_0_4_10 j := by
  revert j
  decide +kernel
lemma tw0_0_4_17_calc (j : Fin 31) : taylorWaveBox 0 0 4 17 j = tw0_0_4_17 j := by
  revert j
  decide +kernel
lemma tw0_0_4_18_calc (j : Fin 31) : taylorWaveBox 0 0 4 18 j = tw0_0_4_18 j := by
  revert j
  decide +kernel
lemma tw0_0_4_19_calc (j : Fin 31) : taylorWaveBox 0 0 4 19 j = tw0_0_4_19 j := by
  revert j
  decide +kernel
lemma tw0_0_4_20_calc (j : Fin 31) : taylorWaveBox 0 0 4 20 j = tw0_0_4_20 j := by
  revert j
  decide +kernel
lemma tw0_0_4_mem_eu_oai (l : Fin 21) (j : Fin 31) : (tw0_0_4 l j).Mem (taylorWave 0 0 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 4 l j = tw0_0_4 l j := by
    fin_cases l
    · exact tw0_0_4_0_calc_eu j
    · exact tw0_0_4_1_calc_eu j
    · exact tw0_0_4_2_calc_eu j
    · exact tw0_0_4_3_calc_eu j
    · exact tw0_0_4_4_calc_eu j
    · exact tw0_0_4_5_calc_eu j
    · exact tw0_0_4_6_calc_eu j
    · exact tw0_0_4_7_calc_eu j
    · exact tw0_0_4_8_calc_eu j
    · exact tw0_0_4_9_calc_eu j
    · exact tw0_0_4_10_calc j
    · exact tw0_0_4_11_calc_eu j
    · exact tw0_0_4_12_calc_eu j
    · exact tw0_0_4_13_calc_eu j
    · exact tw0_0_4_14_calc_eu j
    · exact tw0_0_4_15_calc_eu j
    · exact tw0_0_4_16_calc_eu j
    · exact tw0_0_4_17_calc j
    · exact tw0_0_4_18_calc j
    · exact tw0_0_4_19_calc j
    · exact tw0_0_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 0 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_eu_oai
