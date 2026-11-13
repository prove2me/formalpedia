-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:25:15.06173+00:00
-- url     : https://prove2.me/submissions/70804df0-e222-446d-99d9-a0f57afcce16

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave004
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
lemma tw0_0_4_16_calc (j : Fin 31) : taylorWaveBox 0 0 4 16 j = tw0_0_4_16 j := by
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
lemma tw0_0_4_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw0_0_4 l j).Mem (taylorWave 0 0 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 4 l j = tw0_0_4 l j := by
    fin_cases l
    · exact tw0_0_4_0_calc_x j
    · exact tw0_0_4_1_calc_x j
    · exact tw0_0_4_2_calc_x j
    · exact tw0_0_4_3_calc_x j
    · exact tw0_0_4_4_calc_x j
    · exact tw0_0_4_5_calc_x j
    · exact tw0_0_4_6_calc_x j
    · exact tw0_0_4_7_calc_x j
    · exact tw0_0_4_8_calc_x j
    · exact tw0_0_4_9_calc_x j
    · exact tw0_0_4_10_calc j
    · exact tw0_0_4_11_calc_x j
    · exact tw0_0_4_12_calc_x j
    · exact tw0_0_4_13_calc_x j
    · exact tw0_0_4_14_calc_x j
    · exact tw0_0_4_15_calc_x j
    · exact tw0_0_4_16_calc j
    · exact tw0_0_4_17_calc j
    · exact tw0_0_4_18_calc j
    · exact tw0_0_4_19_calc j
    · exact tw0_0_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 0 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_x_oai
