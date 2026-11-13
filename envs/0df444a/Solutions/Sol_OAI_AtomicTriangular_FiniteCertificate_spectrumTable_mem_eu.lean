-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:29:05.807295+00:00
-- url     : https://prove2.me/submissions/d0f9a01f-dff8-48b2-8f95-6746fabe3f56

import Mathlib
import Definitions.Def_OAIQ334E020
import Definitions.Def_OAIQ334E022
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrumBox_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorSpectrum
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
  exact spectrumBox_mem_eu 0 0 j r
lemma spectrum0_1_0_calc (r : Fin 8) : spectrumBox 0 1 0 r = spectrum0_1_0 r := by
  revert r
  decide +kernel
lemma spectrum0_1_1_calc (r : Fin 8) : spectrumBox 0 1 1 r = spectrum0_1_1 r := by
  revert r
  decide +kernel
lemma spectrum0_1_2_calc (r : Fin 8) : spectrumBox 0 1 2 r = spectrum0_1_2 r := by
  revert r
  decide +kernel
lemma spectrum0_1_3_calc (r : Fin 8) : spectrumBox 0 1 3 r = spectrum0_1_3 r := by
  revert r
  decide +kernel
lemma spectrum0_1_4_calc (r : Fin 8) : spectrumBox 0 1 4 r = spectrum0_1_4 r := by
  revert r
  decide +kernel
lemma spectrum0_1_5_calc (r : Fin 8) : spectrumBox 0 1 5 r = spectrum0_1_5 r := by
  revert r
  decide +kernel
lemma spectrum0_1_6_calc (r : Fin 8) : spectrumBox 0 1 6 r = spectrum0_1_6 r := by
  revert r
  decide +kernel
lemma spectrum0_1_7_calc (r : Fin 8) : spectrumBox 0 1 7 r = spectrum0_1_7 r := by
  revert r
  decide +kernel
lemma spectrum0_1_8_calc (r : Fin 8) : spectrumBox 0 1 8 r = spectrum0_1_8 r := by
  revert r
  decide +kernel
lemma spectrum0_1_9_calc (r : Fin 8) : spectrumBox 0 1 9 r = spectrum0_1_9 r := by
  revert r
  decide +kernel
lemma spectrum0_1_10_calc (r : Fin 8) : spectrumBox 0 1 10 r = spectrum0_1_10 r := by
  revert r
  decide +kernel
lemma spectrum0_1_11_calc (r : Fin 8) : spectrumBox 0 1 11 r = spectrum0_1_11 r := by
  revert r
  decide +kernel
lemma spectrum0_1_12_calc (r : Fin 8) : spectrumBox 0 1 12 r = spectrum0_1_12 r := by
  revert r
  decide +kernel
lemma spectrum0_1_13_calc (r : Fin 8) : spectrumBox 0 1 13 r = spectrum0_1_13 r := by
  revert r
  decide +kernel
lemma spectrum0_1_14_calc (r : Fin 8) : spectrumBox 0 1 14 r = spectrum0_1_14 r := by
  revert r
  decide +kernel
lemma spectrum0_1_15_calc (r : Fin 8) : spectrumBox 0 1 15 r = spectrum0_1_15 r := by
  revert r
  decide +kernel
lemma spectrum0_1_16_calc (r : Fin 8) : spectrumBox 0 1 16 r = spectrum0_1_16 r := by
  revert r
  decide +kernel
lemma spectrum0_1_17_calc (r : Fin 8) : spectrumBox 0 1 17 r = spectrum0_1_17 r := by
  revert r
  decide +kernel
lemma spectrum0_1_18_calc (r : Fin 8) : spectrumBox 0 1 18 r = spectrum0_1_18 r := by
  revert r
  decide +kernel
lemma spectrum0_1_19_calc (r : Fin 8) : spectrumBox 0 1 19 r = spectrum0_1_19 r := by
  revert r
  decide +kernel
lemma spectrum0_1_20_calc (r : Fin 8) : spectrumBox 0 1 20 r = spectrum0_1_20 r := by
  revert r
  decide +kernel
lemma spectrum0_1_21_calc (r : Fin 8) : spectrumBox 0 1 21 r = spectrum0_1_21 r := by
  revert r
  decide +kernel
lemma spectrum0_1_22_calc (r : Fin 8) : spectrumBox 0 1 22 r = spectrum0_1_22 r := by
  revert r
  decide +kernel
lemma spectrum0_1_23_calc (r : Fin 8) : spectrumBox 0 1 23 r = spectrum0_1_23 r := by
  revert r
  decide +kernel
lemma spectrum0_1_24_calc (r : Fin 8) : spectrumBox 0 1 24 r = spectrum0_1_24 r := by
  revert r
  decide +kernel
lemma spectrum0_1_25_calc (r : Fin 8) : spectrumBox 0 1 25 r = spectrum0_1_25 r := by
  revert r
  decide +kernel
lemma spectrum0_1_26_calc (r : Fin 8) : spectrumBox 0 1 26 r = spectrum0_1_26 r := by
  revert r
  decide +kernel
lemma spectrum0_1_27_calc (r : Fin 8) : spectrumBox 0 1 27 r = spectrum0_1_27 r := by
  revert r
  decide +kernel
lemma spectrum0_1_28_calc (r : Fin 8) : spectrumBox 0 1 28 r = spectrum0_1_28 r := by
  revert r
  decide +kernel
lemma spectrum0_1_29_calc (r : Fin 8) : spectrumBox 0 1 29 r = spectrum0_1_29 r := by
  revert r
  decide +kernel
lemma spectrum0_1_30_calc (r : Fin 8) : spectrumBox 0 1 30 r = spectrum0_1_30 r := by
  revert r
  decide +kernel
lemma spectrum0_1_mem (j : Fin 31) (r : Fin 8) : (spectrum0_1 j r).Mem (finiteSpectrum 0 1 j r) := by
  have he : spectrumBox 0 1 j r = spectrum0_1 j r := by
    fin_cases j
    · exact spectrum0_1_0_calc r
    · exact spectrum0_1_1_calc r
    · exact spectrum0_1_2_calc r
    · exact spectrum0_1_3_calc r
    · exact spectrum0_1_4_calc r
    · exact spectrum0_1_5_calc r
    · exact spectrum0_1_6_calc r
    · exact spectrum0_1_7_calc r
    · exact spectrum0_1_8_calc r
    · exact spectrum0_1_9_calc r
    · exact spectrum0_1_10_calc r
    · exact spectrum0_1_11_calc r
    · exact spectrum0_1_12_calc r
    · exact spectrum0_1_13_calc r
    · exact spectrum0_1_14_calc r
    · exact spectrum0_1_15_calc r
    · exact spectrum0_1_16_calc r
    · exact spectrum0_1_17_calc r
    · exact spectrum0_1_18_calc r
    · exact spectrum0_1_19_calc r
    · exact spectrum0_1_20_calc r
    · exact spectrum0_1_21_calc r
    · exact spectrum0_1_22_calc r
    · exact spectrum0_1_23_calc r
    · exact spectrum0_1_24_calc r
    · exact spectrum0_1_25_calc r
    · exact spectrum0_1_26_calc r
    · exact spectrum0_1_27_calc r
    · exact spectrum0_1_28_calc r
    · exact spectrum0_1_29_calc r
    · exact spectrum0_1_30_calc r
  rw [← he]
  exact spectrumBox_mem_eu 0 1 j r
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
  exact spectrumBox_mem_eu 1 0 j r
lemma spectrum1_1_0_calc (r : Fin 8) : spectrumBox 1 1 0 r = spectrum1_1_0 r := by
  revert r
  decide +kernel
lemma spectrum1_1_1_calc (r : Fin 8) : spectrumBox 1 1 1 r = spectrum1_1_1 r := by
  revert r
  decide +kernel
lemma spectrum1_1_2_calc (r : Fin 8) : spectrumBox 1 1 2 r = spectrum1_1_2 r := by
  revert r
  decide +kernel
lemma spectrum1_1_3_calc (r : Fin 8) : spectrumBox 1 1 3 r = spectrum1_1_3 r := by
  revert r
  decide +kernel
lemma spectrum1_1_4_calc (r : Fin 8) : spectrumBox 1 1 4 r = spectrum1_1_4 r := by
  revert r
  decide +kernel
lemma spectrum1_1_5_calc (r : Fin 8) : spectrumBox 1 1 5 r = spectrum1_1_5 r := by
  revert r
  decide +kernel
lemma spectrum1_1_6_calc (r : Fin 8) : spectrumBox 1 1 6 r = spectrum1_1_6 r := by
  revert r
  decide +kernel
lemma spectrum1_1_7_calc (r : Fin 8) : spectrumBox 1 1 7 r = spectrum1_1_7 r := by
  revert r
  decide +kernel
lemma spectrum1_1_8_calc (r : Fin 8) : spectrumBox 1 1 8 r = spectrum1_1_8 r := by
  revert r
  decide +kernel
lemma spectrum1_1_9_calc (r : Fin 8) : spectrumBox 1 1 9 r = spectrum1_1_9 r := by
  revert r
  decide +kernel
lemma spectrum1_1_10_calc (r : Fin 8) : spectrumBox 1 1 10 r = spectrum1_1_10 r := by
  revert r
  decide +kernel
lemma spectrum1_1_11_calc (r : Fin 8) : spectrumBox 1 1 11 r = spectrum1_1_11 r := by
  revert r
  decide +kernel
lemma spectrum1_1_12_calc (r : Fin 8) : spectrumBox 1 1 12 r = spectrum1_1_12 r := by
  revert r
  decide +kernel
lemma spectrum1_1_13_calc (r : Fin 8) : spectrumBox 1 1 13 r = spectrum1_1_13 r := by
  revert r
  decide +kernel
lemma spectrum1_1_14_calc (r : Fin 8) : spectrumBox 1 1 14 r = spectrum1_1_14 r := by
  revert r
  decide +kernel
lemma spectrum1_1_15_calc (r : Fin 8) : spectrumBox 1 1 15 r = spectrum1_1_15 r := by
  revert r
  decide +kernel
lemma spectrum1_1_16_calc (r : Fin 8) : spectrumBox 1 1 16 r = spectrum1_1_16 r := by
  revert r
  decide +kernel
lemma spectrum1_1_17_calc (r : Fin 8) : spectrumBox 1 1 17 r = spectrum1_1_17 r := by
  revert r
  decide +kernel
lemma spectrum1_1_18_calc (r : Fin 8) : spectrumBox 1 1 18 r = spectrum1_1_18 r := by
  revert r
  decide +kernel
lemma spectrum1_1_19_calc (r : Fin 8) : spectrumBox 1 1 19 r = spectrum1_1_19 r := by
  revert r
  decide +kernel
lemma spectrum1_1_20_calc (r : Fin 8) : spectrumBox 1 1 20 r = spectrum1_1_20 r := by
  revert r
  decide +kernel
lemma spectrum1_1_21_calc (r : Fin 8) : spectrumBox 1 1 21 r = spectrum1_1_21 r := by
  revert r
  decide +kernel
lemma spectrum1_1_22_calc (r : Fin 8) : spectrumBox 1 1 22 r = spectrum1_1_22 r := by
  revert r
  decide +kernel
lemma spectrum1_1_23_calc (r : Fin 8) : spectrumBox 1 1 23 r = spectrum1_1_23 r := by
  revert r
  decide +kernel
lemma spectrum1_1_24_calc (r : Fin 8) : spectrumBox 1 1 24 r = spectrum1_1_24 r := by
  revert r
  decide +kernel
lemma spectrum1_1_25_calc (r : Fin 8) : spectrumBox 1 1 25 r = spectrum1_1_25 r := by
  revert r
  decide +kernel
lemma spectrum1_1_26_calc (r : Fin 8) : spectrumBox 1 1 26 r = spectrum1_1_26 r := by
  revert r
  decide +kernel
lemma spectrum1_1_27_calc (r : Fin 8) : spectrumBox 1 1 27 r = spectrum1_1_27 r := by
  revert r
  decide +kernel
lemma spectrum1_1_28_calc (r : Fin 8) : spectrumBox 1 1 28 r = spectrum1_1_28 r := by
  revert r
  decide +kernel
lemma spectrum1_1_29_calc (r : Fin 8) : spectrumBox 1 1 29 r = spectrum1_1_29 r := by
  revert r
  decide +kernel
lemma spectrum1_1_30_calc (r : Fin 8) : spectrumBox 1 1 30 r = spectrum1_1_30 r := by
  revert r
  decide +kernel
lemma spectrum1_1_mem (j : Fin 31) (r : Fin 8) : (spectrum1_1 j r).Mem (finiteSpectrum 1 1 j r) := by
  have he : spectrumBox 1 1 j r = spectrum1_1 j r := by
    fin_cases j
    · exact spectrum1_1_0_calc r
    · exact spectrum1_1_1_calc r
    · exact spectrum1_1_2_calc r
    · exact spectrum1_1_3_calc r
    · exact spectrum1_1_4_calc r
    · exact spectrum1_1_5_calc r
    · exact spectrum1_1_6_calc r
    · exact spectrum1_1_7_calc r
    · exact spectrum1_1_8_calc r
    · exact spectrum1_1_9_calc r
    · exact spectrum1_1_10_calc r
    · exact spectrum1_1_11_calc r
    · exact spectrum1_1_12_calc r
    · exact spectrum1_1_13_calc r
    · exact spectrum1_1_14_calc r
    · exact spectrum1_1_15_calc r
    · exact spectrum1_1_16_calc r
    · exact spectrum1_1_17_calc r
    · exact spectrum1_1_18_calc r
    · exact spectrum1_1_19_calc r
    · exact spectrum1_1_20_calc r
    · exact spectrum1_1_21_calc r
    · exact spectrum1_1_22_calc r
    · exact spectrum1_1_23_calc r
    · exact spectrum1_1_24_calc r
    · exact spectrum1_1_25_calc r
    · exact spectrum1_1_26_calc r
    · exact spectrum1_1_27_calc r
    · exact spectrum1_1_28_calc r
    · exact spectrum1_1_29_calc r
    · exact spectrum1_1_30_calc r
  rw [← he]
  exact spectrumBox_mem_eu 1 1 j r
lemma spectrumTable_mem_eu_oai (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
    (spectrumTable side q j r).Mem (finiteSpectrum side q j r) := by
  fin_cases side <;> fin_cases q
  · exact spectrum0_0_mem j r
  · exact spectrum0_1_mem j r
  · exact spectrum1_0_mem j r
  · exact spectrum1_1_mem j r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_eu_oai
