-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:22:23.378459+00:00
-- url     : https://prove2.me/submissions/b719f8c6-6c6a-4ad6-9dd8-098ac2ee7410

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_2_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_3_9_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_5_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_6_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_3_16_calc (j : Fin 31) : taylorWaveBox 1 1 3 16 j = tw1_1_3_16 j := by
  revert j
  decide +kernel
lemma tw1_1_3_17_calc (j : Fin 31) : taylorWaveBox 1 1 3 17 j = tw1_1_3_17 j := by
  revert j
  decide +kernel
lemma tw1_1_3_18_calc (j : Fin 31) : taylorWaveBox 1 1 3 18 j = tw1_1_3_18 j := by
  revert j
  decide +kernel
lemma tw1_1_3_19_calc (j : Fin 31) : taylorWaveBox 1 1 3 19 j = tw1_1_3_19 j := by
  revert j
  decide +kernel
lemma tw1_1_3_20_calc (j : Fin 31) : taylorWaveBox 1 1 3 20 j = tw1_1_3_20 j := by
  revert j
  decide +kernel
lemma tw1_1_3_mem (l : Fin 21) (j : Fin 31) : (tw1_1_3 l j).Mem (taylorWave 1 1 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 3 l j = tw1_1_3 l j := by
    fin_cases l
    · exact tw1_1_3_0_calc_eu j
    · exact tw1_1_3_1_calc_eu j
    · exact tw1_1_3_2_calc_eu j
    · exact tw1_1_3_3_calc_eu j
    · exact tw1_1_3_4_calc_eu j
    · exact tw1_1_3_5_calc_eu j
    · exact tw1_1_3_6_calc_eu j
    · exact tw1_1_3_7_calc_eu j
    · exact tw1_1_3_8_calc_eu j
    · exact tw1_1_3_9_calc_eu j
    · exact tw1_1_3_10_calc_eu j
    · exact tw1_1_3_11_calc_eu j
    · exact tw1_1_3_12_calc_eu j
    · exact tw1_1_3_13_calc_eu j
    · exact tw1_1_3_14_calc_eu j
    · exact tw1_1_3_15_calc_eu j
    · exact tw1_1_3_16_calc j
    · exact tw1_1_3_17_calc j
    · exact tw1_1_3_18_calc j
    · exact tw1_1_3_19_calc j
    · exact tw1_1_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 1 1 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_mem_eu_oai (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_1 n l j).Mem (taylorWave 1 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_1_0_mem_eu l j
  · exact tw1_1_1_mem_eu l j
  · exact tw1_1_2_mem_eu l j
  · exact tw1_1_3_mem l j
  · exact tw1_1_4_mem_eu l j
  · exact tw1_1_5_mem_eu l j
  · exact tw1_1_6_mem_eu l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_eu_oai
