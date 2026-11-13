-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:56:52.317556+00:00
-- url     : https://prove2.me/submissions/380c0954-e7af-4533-9689-025d22481dd7

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_19_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_20_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_1_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_1_0_calc (j : Fin 31) : taylorWaveBox 1 1 1 0 j = tw1_1_1_0 j := by
  revert j
  decide +kernel
lemma tw1_1_1_10_calc (j : Fin 31) : taylorWaveBox 1 1 1 10 j = tw1_1_1_10 j := by
  revert j
  decide +kernel
lemma tw1_1_1_11_calc (j : Fin 31) : taylorWaveBox 1 1 1 11 j = tw1_1_1_11 j := by
  revert j
  decide +kernel
lemma tw1_1_1_12_calc (j : Fin 31) : taylorWaveBox 1 1 1 12 j = tw1_1_1_12 j := by
  revert j
  decide +kernel
lemma tw1_1_1_13_calc (j : Fin 31) : taylorWaveBox 1 1 1 13 j = tw1_1_1_13 j := by
  revert j
  decide +kernel
lemma tw1_1_1_14_calc (j : Fin 31) : taylorWaveBox 1 1 1 14 j = tw1_1_1_14 j := by
  revert j
  decide +kernel
lemma tw1_1_1_mem_x_oai (l : Fin 21) (j : Fin 31) : (tw1_1_1 l j).Mem (taylorWave 1 1 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 1 l j = tw1_1_1 l j := by
    fin_cases l
    · exact tw1_1_1_0_calc j
    · exact tw1_1_1_1_calc_x j
    · exact tw1_1_1_2_calc_x j
    · exact tw1_1_1_3_calc_x j
    · exact tw1_1_1_4_calc_x j
    · exact tw1_1_1_5_calc_x j
    · exact tw1_1_1_6_calc_x j
    · exact tw1_1_1_7_calc_x j
    · exact tw1_1_1_8_calc_x j
    · exact tw1_1_1_9_calc_x j
    · exact tw1_1_1_10_calc j
    · exact tw1_1_1_11_calc j
    · exact tw1_1_1_12_calc j
    · exact tw1_1_1_13_calc j
    · exact tw1_1_1_14_calc j
    · exact tw1_1_1_15_calc_x j
    · exact tw1_1_1_16_calc_x j
    · exact tw1_1_1_17_calc_x j
    · exact tw1_1_1_18_calc_x j
    · exact tw1_1_1_19_calc_x j
    · exact tw1_1_1_20_calc_x j
  rw [← he]
  exact taylorWaveBox_mem_x 1 1 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_x_oai
