-- Prove2me | solution 1 for HuangN13.N13SpecialSmallFunctionCertificate.supported_small_function_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:25:20.427748+00:00
-- url     : https://prove2.me/submissions/c29fba9f-3b1a-47f4-b0b0-5c6b5ebf5968

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_00_01
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_02_03
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_04_05
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_06_07
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_08_09
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_10_11
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_12_13
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_14_15
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_16_17
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_18_19
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_20_21
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_22_23
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_24_25
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_26_27
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_28_29
import Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_30_31

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSmallFunctionCertificate
noncomputable section
open Polynomial
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem huangN13CertificateAssembly : ∀ (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K), MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate a b := by
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_00_01 with ⟨row_0_0, row_0_1, row_0_2, row_0_3, row_1_0, row_1_1, row_1_2, row_1_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_02_03 with ⟨row_2_0, row_2_1, row_2_2, row_2_3, row_3_0, row_3_1, row_3_2, row_3_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_04_05 with ⟨row_4_0, row_4_1, row_4_2, row_4_3, row_5_0, row_5_1, row_5_2, row_5_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_06_07 with ⟨row_6_0, row_6_1, row_6_2, row_6_3, row_7_0, row_7_1, row_7_2, row_7_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_08_09 with ⟨row_8_0, row_8_1, row_8_2, row_8_3, row_9_0, row_9_1, row_9_2, row_9_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_10_11 with ⟨row_10_0, row_10_1, row_10_2, row_10_3, row_11_0, row_11_1, row_11_2, row_11_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_12_13 with ⟨row_12_0, row_12_1, row_12_2, row_12_3, row_13_0, row_13_1, row_13_2, row_13_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_14_15 with ⟨row_14_0, row_14_1, row_14_2, row_14_3, row_15_0, row_15_1, row_15_2, row_15_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_16_17 with ⟨row_16_0, row_16_1, row_16_2, row_16_3, row_17_0, row_17_1, row_17_2, row_17_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_18_19 with ⟨row_18_0, row_18_1, row_18_2, row_18_3, row_19_0, row_19_1, row_19_2, row_19_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_20_21 with ⟨row_20_0, row_20_1, row_20_2, row_20_3, row_21_0, row_21_1, row_21_2, row_21_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_22_23 with ⟨row_22_0, row_22_1, row_22_2, row_22_3, row_23_0, row_23_1, row_23_2, row_23_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_24_25 with ⟨row_24_0, row_24_1, row_24_2, row_24_3, row_25_0, row_25_1, row_25_2, row_25_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_26_27 with ⟨row_26_0, row_26_1, row_26_2, row_26_3, row_27_0, row_27_1, row_27_2, row_27_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_28_29 with ⟨row_28_0, row_28_1, row_28_2, row_28_3, row_29_0, row_29_1, row_29_2, row_29_3⟩
  rcases HuangN13.N13SpecialSmallFunctionCertificate.rows_30_31 with ⟨row_30_0, row_30_1, row_30_2, row_30_3, row_31_0, row_31_1, row_31_2, row_31_3⟩
  intro a b
  change PairCertificate a b
  have ha : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, hb]
  rcases binary (a 0) with h0 | h0 <;>
    rcases binary (a 1) with h1 | h1 <;>
    rcases binary (a 2) with h2 | h2 <;>
    rcases binary (a 3) with h3 | h3 <;>
    rcases binary (a 4) with h4 | h4 <;>
    rcases binary (b 0) with k0 | k0 <;>
    rcases binary (b 1) with k1 | k1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_3
end
end MazurProof.N13SpecialSmallFunctionCertificate
end
end

theorem solution : ∀ (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K), MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate a b := by
  exact MazurProof.N13SpecialSmallFunctionCertificate.huangN13CertificateAssembly
