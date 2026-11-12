-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:37:35.38487+00:00
-- url     : https://prove2.me/submissions/440fb076-d455-4f4c-8b16-e4e46675bbd1

import Mathlib
import Definitions.Def_OAIQ257X020
import Definitions.Def_OAIQ257X022
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrum0_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrum1_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrumBox_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma spectrum0_0_0_calc (r : Fin 8) : spectrumBox 0 0 0 r = spectrum0_0_0 r := by
  revert r
  decide +kernel
lemma spectrum0_0_1_calc (r : Fin 8) : spectrumBox 0 0 1 r = spectrum0_0_1 r := by
  revert r
  decide +kernel
lemma spectrum0_0_2_calc (r : Fin 8) : spectrumBox 0 0 2 r = spectrum0_0_2 r := by
  revert r
  decide +kernel
lemma spectrum0_0_3_calc (r : Fin 8) : spectrumBox 0 0 3 r = spectrum0_0_3 r := by
  revert r
  decide +kernel
lemma spectrum0_0_4_calc (r : Fin 8) : spectrumBox 0 0 4 r = spectrum0_0_4 r := by
  revert r
  decide +kernel
lemma spectrum0_0_5_calc (r : Fin 8) : spectrumBox 0 0 5 r = spectrum0_0_5 r := by
  revert r
  decide +kernel
lemma spectrum0_0_6_calc (r : Fin 8) : spectrumBox 0 0 6 r = spectrum0_0_6 r := by
  revert r
  decide +kernel
lemma spectrum0_0_7_calc (r : Fin 8) : spectrumBox 0 0 7 r = spectrum0_0_7 r := by
  revert r
  decide +kernel
lemma spectrum0_0_8_calc (r : Fin 8) : spectrumBox 0 0 8 r = spectrum0_0_8 r := by
  revert r
  decide +kernel
lemma spectrum0_0_9_calc (r : Fin 8) : spectrumBox 0 0 9 r = spectrum0_0_9 r := by
  revert r
  decide +kernel
lemma spectrum0_0_10_calc (r : Fin 8) : spectrumBox 0 0 10 r = spectrum0_0_10 r := by
  revert r
  decide +kernel
lemma spectrum0_0_11_calc (r : Fin 8) : spectrumBox 0 0 11 r = spectrum0_0_11 r := by
  revert r
  decide +kernel
lemma spectrum0_0_12_calc (r : Fin 8) : spectrumBox 0 0 12 r = spectrum0_0_12 r := by
  revert r
  decide +kernel
lemma spectrum0_0_13_calc (r : Fin 8) : spectrumBox 0 0 13 r = spectrum0_0_13 r := by
  revert r
  decide +kernel
lemma spectrum0_0_14_calc (r : Fin 8) : spectrumBox 0 0 14 r = spectrum0_0_14 r := by
  revert r
  decide +kernel
lemma spectrum0_0_15_calc (r : Fin 8) : spectrumBox 0 0 15 r = spectrum0_0_15 r := by
  revert r
  decide +kernel
lemma spectrum0_0_16_calc (r : Fin 8) : spectrumBox 0 0 16 r = spectrum0_0_16 r := by
  revert r
  decide +kernel
lemma spectrum0_0_17_calc (r : Fin 8) : spectrumBox 0 0 17 r = spectrum0_0_17 r := by
  revert r
  decide +kernel
lemma spectrum0_0_18_calc (r : Fin 8) : spectrumBox 0 0 18 r = spectrum0_0_18 r := by
  revert r
  decide +kernel
lemma spectrum0_0_19_calc (r : Fin 8) : spectrumBox 0 0 19 r = spectrum0_0_19 r := by
  revert r
  decide +kernel
lemma spectrum0_0_20_calc (r : Fin 8) : spectrumBox 0 0 20 r = spectrum0_0_20 r := by
  revert r
  decide +kernel
lemma spectrum0_0_21_calc (r : Fin 8) : spectrumBox 0 0 21 r = spectrum0_0_21 r := by
  revert r
  decide +kernel
lemma spectrum0_0_22_calc (r : Fin 8) : spectrumBox 0 0 22 r = spectrum0_0_22 r := by
  revert r
  decide +kernel
lemma spectrum0_0_23_calc (r : Fin 8) : spectrumBox 0 0 23 r = spectrum0_0_23 r := by
  revert r
  decide +kernel
lemma spectrum0_0_24_calc (r : Fin 8) : spectrumBox 0 0 24 r = spectrum0_0_24 r := by
  revert r
  decide +kernel
lemma spectrum0_0_25_calc (r : Fin 8) : spectrumBox 0 0 25 r = spectrum0_0_25 r := by
  revert r
  decide +kernel
lemma spectrum0_0_26_calc (r : Fin 8) : spectrumBox 0 0 26 r = spectrum0_0_26 r := by
  revert r
  decide +kernel
lemma spectrum0_0_27_calc (r : Fin 8) : spectrumBox 0 0 27 r = spectrum0_0_27 r := by
  revert r
  decide +kernel
lemma spectrum0_0_28_calc (r : Fin 8) : spectrumBox 0 0 28 r = spectrum0_0_28 r := by
  revert r
  decide +kernel
lemma spectrum0_0_29_calc (r : Fin 8) : spectrumBox 0 0 29 r = spectrum0_0_29 r := by
  revert r
  decide +kernel
lemma spectrum0_0_30_calc (r : Fin 8) : spectrumBox 0 0 30 r = spectrum0_0_30 r := by
  revert r
  decide +kernel
lemma spectrum0_0_mem (j : Fin 31) (r : Fin 8) : (spectrum0_0 j r).Mem (finiteSpectrum 0 0 j r) := by
  have he : spectrumBox 0 0 j r = spectrum0_0 j r := by
    fin_cases j
    · exact spectrum0_0_0_calc r
    · exact spectrum0_0_1_calc r
    · exact spectrum0_0_2_calc r
    · exact spectrum0_0_3_calc r
    · exact spectrum0_0_4_calc r
    · exact spectrum0_0_5_calc r
    · exact spectrum0_0_6_calc r
    · exact spectrum0_0_7_calc r
    · exact spectrum0_0_8_calc r
    · exact spectrum0_0_9_calc r
    · exact spectrum0_0_10_calc r
    · exact spectrum0_0_11_calc r
    · exact spectrum0_0_12_calc r
    · exact spectrum0_0_13_calc r
    · exact spectrum0_0_14_calc r
    · exact spectrum0_0_15_calc r
    · exact spectrum0_0_16_calc r
    · exact spectrum0_0_17_calc r
    · exact spectrum0_0_18_calc r
    · exact spectrum0_0_19_calc r
    · exact spectrum0_0_20_calc r
    · exact spectrum0_0_21_calc r
    · exact spectrum0_0_22_calc r
    · exact spectrum0_0_23_calc r
    · exact spectrum0_0_24_calc r
    · exact spectrum0_0_25_calc r
    · exact spectrum0_0_26_calc r
    · exact spectrum0_0_27_calc r
    · exact spectrum0_0_28_calc r
    · exact spectrum0_0_29_calc r
    · exact spectrum0_0_30_calc r
  rw [← he]
  exact spectrumBox_mem_x 0 0 j r
lemma spectrum1_0_0_calc (r : Fin 8) : spectrumBox 1 0 0 r = spectrum1_0_0 r := by
  revert r
  decide +kernel
lemma spectrum1_0_1_calc (r : Fin 8) : spectrumBox 1 0 1 r = spectrum1_0_1 r := by
  revert r
  decide +kernel
lemma spectrum1_0_2_calc (r : Fin 8) : spectrumBox 1 0 2 r = spectrum1_0_2 r := by
  revert r
  decide +kernel
lemma spectrum1_0_3_calc (r : Fin 8) : spectrumBox 1 0 3 r = spectrum1_0_3 r := by
  revert r
  decide +kernel
lemma spectrum1_0_4_calc (r : Fin 8) : spectrumBox 1 0 4 r = spectrum1_0_4 r := by
  revert r
  decide +kernel
lemma spectrum1_0_5_calc (r : Fin 8) : spectrumBox 1 0 5 r = spectrum1_0_5 r := by
  revert r
  decide +kernel
lemma spectrum1_0_6_calc (r : Fin 8) : spectrumBox 1 0 6 r = spectrum1_0_6 r := by
  revert r
  decide +kernel
lemma spectrum1_0_7_calc (r : Fin 8) : spectrumBox 1 0 7 r = spectrum1_0_7 r := by
  revert r
  decide +kernel
lemma spectrum1_0_8_calc (r : Fin 8) : spectrumBox 1 0 8 r = spectrum1_0_8 r := by
  revert r
  decide +kernel
lemma spectrum1_0_9_calc (r : Fin 8) : spectrumBox 1 0 9 r = spectrum1_0_9 r := by
  revert r
  decide +kernel
lemma spectrum1_0_10_calc (r : Fin 8) : spectrumBox 1 0 10 r = spectrum1_0_10 r := by
  revert r
  decide +kernel
lemma spectrum1_0_11_calc (r : Fin 8) : spectrumBox 1 0 11 r = spectrum1_0_11 r := by
  revert r
  decide +kernel
lemma spectrum1_0_12_calc (r : Fin 8) : spectrumBox 1 0 12 r = spectrum1_0_12 r := by
  revert r
  decide +kernel
lemma spectrum1_0_13_calc (r : Fin 8) : spectrumBox 1 0 13 r = spectrum1_0_13 r := by
  revert r
  decide +kernel
lemma spectrum1_0_14_calc (r : Fin 8) : spectrumBox 1 0 14 r = spectrum1_0_14 r := by
  revert r
  decide +kernel
lemma spectrum1_0_15_calc (r : Fin 8) : spectrumBox 1 0 15 r = spectrum1_0_15 r := by
  revert r
  decide +kernel
lemma spectrum1_0_16_calc (r : Fin 8) : spectrumBox 1 0 16 r = spectrum1_0_16 r := by
  revert r
  decide +kernel
lemma spectrum1_0_17_calc (r : Fin 8) : spectrumBox 1 0 17 r = spectrum1_0_17 r := by
  revert r
  decide +kernel
lemma spectrum1_0_18_calc (r : Fin 8) : spectrumBox 1 0 18 r = spectrum1_0_18 r := by
  revert r
  decide +kernel
lemma spectrum1_0_19_calc (r : Fin 8) : spectrumBox 1 0 19 r = spectrum1_0_19 r := by
  revert r
  decide +kernel
lemma spectrum1_0_20_calc (r : Fin 8) : spectrumBox 1 0 20 r = spectrum1_0_20 r := by
  revert r
  decide +kernel
lemma spectrum1_0_21_calc (r : Fin 8) : spectrumBox 1 0 21 r = spectrum1_0_21 r := by
  revert r
  decide +kernel
lemma spectrum1_0_22_calc (r : Fin 8) : spectrumBox 1 0 22 r = spectrum1_0_22 r := by
  revert r
  decide +kernel
lemma spectrum1_0_23_calc (r : Fin 8) : spectrumBox 1 0 23 r = spectrum1_0_23 r := by
  revert r
  decide +kernel
lemma spectrum1_0_24_calc (r : Fin 8) : spectrumBox 1 0 24 r = spectrum1_0_24 r := by
  revert r
  decide +kernel
lemma spectrum1_0_25_calc (r : Fin 8) : spectrumBox 1 0 25 r = spectrum1_0_25 r := by
  revert r
  decide +kernel
lemma spectrum1_0_26_calc (r : Fin 8) : spectrumBox 1 0 26 r = spectrum1_0_26 r := by
  revert r
  decide +kernel
lemma spectrum1_0_27_calc (r : Fin 8) : spectrumBox 1 0 27 r = spectrum1_0_27 r := by
  revert r
  decide +kernel
lemma spectrum1_0_28_calc (r : Fin 8) : spectrumBox 1 0 28 r = spectrum1_0_28 r := by
  revert r
  decide +kernel
lemma spectrum1_0_29_calc (r : Fin 8) : spectrumBox 1 0 29 r = spectrum1_0_29 r := by
  revert r
  decide +kernel
lemma spectrum1_0_30_calc (r : Fin 8) : spectrumBox 1 0 30 r = spectrum1_0_30 r := by
  revert r
  decide +kernel
lemma spectrum1_0_mem (j : Fin 31) (r : Fin 8) : (spectrum1_0 j r).Mem (finiteSpectrum 1 0 j r) := by
  have he : spectrumBox 1 0 j r = spectrum1_0 j r := by
    fin_cases j
    · exact spectrum1_0_0_calc r
    · exact spectrum1_0_1_calc r
    · exact spectrum1_0_2_calc r
    · exact spectrum1_0_3_calc r
    · exact spectrum1_0_4_calc r
    · exact spectrum1_0_5_calc r
    · exact spectrum1_0_6_calc r
    · exact spectrum1_0_7_calc r
    · exact spectrum1_0_8_calc r
    · exact spectrum1_0_9_calc r
    · exact spectrum1_0_10_calc r
    · exact spectrum1_0_11_calc r
    · exact spectrum1_0_12_calc r
    · exact spectrum1_0_13_calc r
    · exact spectrum1_0_14_calc r
    · exact spectrum1_0_15_calc r
    · exact spectrum1_0_16_calc r
    · exact spectrum1_0_17_calc r
    · exact spectrum1_0_18_calc r
    · exact spectrum1_0_19_calc r
    · exact spectrum1_0_20_calc r
    · exact spectrum1_0_21_calc r
    · exact spectrum1_0_22_calc r
    · exact spectrum1_0_23_calc r
    · exact spectrum1_0_24_calc r
    · exact spectrum1_0_25_calc r
    · exact spectrum1_0_26_calc r
    · exact spectrum1_0_27_calc r
    · exact spectrum1_0_28_calc r
    · exact spectrum1_0_29_calc r
    · exact spectrum1_0_30_calc r
  rw [← he]
  exact spectrumBox_mem_x 1 0 j r
lemma spectrumTable_mem_x_oai (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
    (spectrumTable side q j r).Mem (finiteSpectrum side q j r) := by
  fin_cases side <;> fin_cases q
  · exact spectrum0_0_mem j r
  · exact spectrum0_1_mem_x j r
  · exact spectrum1_0_mem j r
  · exact spectrum1_1_mem_x j r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_x_oai
