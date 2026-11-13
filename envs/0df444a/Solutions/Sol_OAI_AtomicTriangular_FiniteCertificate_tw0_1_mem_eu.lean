-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:59:15.112885+00:00
-- url     : https://prove2.me/submissions/9e9d3219-37f8-4e65-8a9c-686a655f1712

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_1_9_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_2_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_5_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_6_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave011
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
    · exact tw0_1_1_0_calc_eu j
    · exact tw0_1_1_1_calc_eu j
    · exact tw0_1_1_2_calc_eu j
    · exact tw0_1_1_3_calc_eu j
    · exact tw0_1_1_4_calc_eu j
    · exact tw0_1_1_5_calc_eu j
    · exact tw0_1_1_6_calc_eu j
    · exact tw0_1_1_7_calc_eu j
    · exact tw0_1_1_8_calc_eu j
    · exact tw0_1_1_9_calc_eu j
    · exact tw0_1_1_10_calc_eu j
    · exact tw0_1_1_11_calc_eu j
    · exact tw0_1_1_12_calc_eu j
    · exact tw0_1_1_13_calc_eu j
    · exact tw0_1_1_14_calc_eu j
    · exact tw0_1_1_15_calc_eu j
    · exact tw0_1_1_16_calc j
    · exact tw0_1_1_17_calc j
    · exact tw0_1_1_18_calc j
    · exact tw0_1_1_19_calc j
    · exact tw0_1_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_eu 0 1 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_mem_eu_oai (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_1 n l j).Mem (taylorWave 0 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_1_0_mem_eu l j
  · exact tw0_1_1_mem l j
  · exact tw0_1_2_mem_eu l j
  · exact tw0_1_3_mem_eu l j
  · exact tw0_1_4_mem_eu l j
  · exact tw0_1_5_mem_eu l j
  · exact tw0_1_6_mem_eu l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_eu_oai
