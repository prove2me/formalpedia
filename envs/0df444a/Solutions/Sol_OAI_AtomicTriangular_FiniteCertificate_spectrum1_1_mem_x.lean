-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.spectrum1_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:37:33.022728+00:00
-- url     : https://prove2.me/submissions/33ea0504-15ae-4e73-bccc-f3830cc5f4ae

import Mathlib
import Definitions.Def_OAIQ257X020
import Definitions.Def_OAIQ257X022
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
lemma spectrum1_1_mem_x_oai (j : Fin 31) (r : Fin 8) : (spectrum1_1 j r).Mem (finiteSpectrum 1 1 j r) := by
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
  exact spectrumBox_mem_x 1 1 j r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.spectrum1_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.spectrum1_1_mem_x_oai
