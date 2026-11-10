-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hk0_1_9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:46:06.696193+00:00
-- url     : https://prove2.me/submissions/079d45e4-457e-4a38-8cd0-637086c26dd8

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G477
import Definitions.Def_OAIQ098G1405
import Definitions.Def_OAIQ098G1680
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_9_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans0_contains (j : Fin 6) (i k : Fin 16) :
    (trans0 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(0:ℕ))) := by
  simpa only [trans0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num))
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel0_0_r0_0_eq : ∀ k : Fin 16, kernel0_0Expr 0 0 k = kernel0_0_r0_0 k := by decide +kernel
lemma kernel0_0_r0_1_eq : ∀ k : Fin 16, kernel0_0Expr 0 1 k = kernel0_0_r0_1 k := by decide +kernel
lemma kernel0_0_r0_2_eq : ∀ k : Fin 16, kernel0_0Expr 0 2 k = kernel0_0_r0_2 k := by decide +kernel
lemma kernel0_0_r0_3_eq : ∀ k : Fin 16, kernel0_0Expr 0 3 k = kernel0_0_r0_3 k := by decide +kernel
lemma kernel0_0_r0_4_eq : ∀ k : Fin 16, kernel0_0Expr 0 4 k = kernel0_0_r0_4 k := by decide +kernel
lemma kernel0_0_r0_5_eq : ∀ k : Fin 16, kernel0_0Expr 0 5 k = kernel0_0_r0_5 k := by decide +kernel
lemma kernel0_0_r0_6_eq : ∀ k : Fin 16, kernel0_0Expr 0 6 k = kernel0_0_r0_6 k := by decide +kernel
lemma kernel0_0_r0_7_eq : ∀ k : Fin 16, kernel0_0Expr 0 7 k = kernel0_0_r0_7 k := by decide +kernel
lemma kernel0_0_r0_8_eq : ∀ k : Fin 16, kernel0_0Expr 0 8 k = kernel0_0_r0_8 k := by decide +kernel
lemma kernel0_0_r0_9_eq : ∀ k : Fin 16, kernel0_0Expr 0 9 k = kernel0_0_r0_9 k := by decide +kernel
lemma kernel0_0_r0_10_eq : ∀ k : Fin 16, kernel0_0Expr 0 10 k = kernel0_0_r0_10 k := by decide +kernel
lemma kernel0_0_r0_11_eq : ∀ k : Fin 16, kernel0_0Expr 0 11 k = kernel0_0_r0_11 k := by decide +kernel
lemma kernel0_0_r0_12_eq : ∀ k : Fin 16, kernel0_0Expr 0 12 k = kernel0_0_r0_12 k := by decide +kernel
lemma kernel0_0_r0_13_eq : ∀ k : Fin 16, kernel0_0Expr 0 13 k = kernel0_0_r0_13 k := by decide +kernel
lemma kernel0_0_r0_14_eq : ∀ k : Fin 16, kernel0_0Expr 0 14 k = kernel0_0_r0_14 k := by decide +kernel
lemma kernel0_0_r0_15_eq : ∀ k : Fin 16, kernel0_0Expr 0 15 k = kernel0_0_r0_15 k := by decide +kernel
lemma kernel0_0_r0_eq (i k : Fin 16) : kernel0_0Expr 0 i k = kernel0_0_r0 i k := by
  fin_cases i
  · exact kernel0_0_r0_0_eq k
  · exact kernel0_0_r0_1_eq k
  · exact kernel0_0_r0_2_eq k
  · exact kernel0_0_r0_3_eq k
  · exact kernel0_0_r0_4_eq k
  · exact kernel0_0_r0_5_eq k
  · exact kernel0_0_r0_6_eq k
  · exact kernel0_0_r0_7_eq k
  · exact kernel0_0_r0_8_eq k
  · exact kernel0_0_r0_9_eq k
  · exact kernel0_0_r0_10_eq k
  · exact kernel0_0_r0_11_eq k
  · exact kernel0_0_r0_12_eq k
  · exact kernel0_0_r0_13_eq k
  · exact kernel0_0_r0_14_eq k
  · exact kernel0_0_r0_15_eq k
lemma kernel0_0_r1_0_eq : ∀ k : Fin 16, kernel0_0Expr 1 0 k = kernel0_0_r1_0 k := by decide +kernel
lemma kernel0_0_r1_1_eq : ∀ k : Fin 16, kernel0_0Expr 1 1 k = kernel0_0_r1_1 k := by decide +kernel
lemma kernel0_0_r1_2_eq : ∀ k : Fin 16, kernel0_0Expr 1 2 k = kernel0_0_r1_2 k := by decide +kernel
lemma kernel0_0_r1_3_eq : ∀ k : Fin 16, kernel0_0Expr 1 3 k = kernel0_0_r1_3 k := by decide +kernel
lemma kernel0_0_r1_4_eq : ∀ k : Fin 16, kernel0_0Expr 1 4 k = kernel0_0_r1_4 k := by decide +kernel
lemma kernel0_0_r1_5_eq : ∀ k : Fin 16, kernel0_0Expr 1 5 k = kernel0_0_r1_5 k := by decide +kernel
lemma kernel0_0_r1_6_eq : ∀ k : Fin 16, kernel0_0Expr 1 6 k = kernel0_0_r1_6 k := by decide +kernel
lemma kernel0_0_r1_7_eq : ∀ k : Fin 16, kernel0_0Expr 1 7 k = kernel0_0_r1_7 k := by decide +kernel
lemma kernel0_0_r1_8_eq : ∀ k : Fin 16, kernel0_0Expr 1 8 k = kernel0_0_r1_8 k := by decide +kernel
lemma kernel0_0_r1_9_eq : ∀ k : Fin 16, kernel0_0Expr 1 9 k = kernel0_0_r1_9 k := by decide +kernel
lemma kernel0_0_r1_10_eq : ∀ k : Fin 16, kernel0_0Expr 1 10 k = kernel0_0_r1_10 k := by decide +kernel
lemma kernel0_0_r1_11_eq : ∀ k : Fin 16, kernel0_0Expr 1 11 k = kernel0_0_r1_11 k := by decide +kernel
lemma kernel0_0_r1_12_eq : ∀ k : Fin 16, kernel0_0Expr 1 12 k = kernel0_0_r1_12 k := by decide +kernel
lemma kernel0_0_r1_13_eq : ∀ k : Fin 16, kernel0_0Expr 1 13 k = kernel0_0_r1_13 k := by decide +kernel
lemma kernel0_0_r1_14_eq : ∀ k : Fin 16, kernel0_0Expr 1 14 k = kernel0_0_r1_14 k := by decide +kernel
lemma kernel0_0_r1_15_eq : ∀ k : Fin 16, kernel0_0Expr 1 15 k = kernel0_0_r1_15 k := by decide +kernel
lemma kernel0_0_r1_eq (i k : Fin 16) : kernel0_0Expr 1 i k = kernel0_0_r1 i k := by
  fin_cases i
  · exact kernel0_0_r1_0_eq k
  · exact kernel0_0_r1_1_eq k
  · exact kernel0_0_r1_2_eq k
  · exact kernel0_0_r1_3_eq k
  · exact kernel0_0_r1_4_eq k
  · exact kernel0_0_r1_5_eq k
  · exact kernel0_0_r1_6_eq k
  · exact kernel0_0_r1_7_eq k
  · exact kernel0_0_r1_8_eq k
  · exact kernel0_0_r1_9_eq k
  · exact kernel0_0_r1_10_eq k
  · exact kernel0_0_r1_11_eq k
  · exact kernel0_0_r1_12_eq k
  · exact kernel0_0_r1_13_eq k
  · exact kernel0_0_r1_14_eq k
  · exact kernel0_0_r1_15_eq k
lemma kernel0_0_r2_0_eq : ∀ k : Fin 16, kernel0_0Expr 2 0 k = kernel0_0_r2_0 k := by decide +kernel
lemma kernel0_0_r2_1_eq : ∀ k : Fin 16, kernel0_0Expr 2 1 k = kernel0_0_r2_1 k := by decide +kernel
lemma kernel0_0_r2_2_eq : ∀ k : Fin 16, kernel0_0Expr 2 2 k = kernel0_0_r2_2 k := by decide +kernel
lemma kernel0_0_r2_3_eq : ∀ k : Fin 16, kernel0_0Expr 2 3 k = kernel0_0_r2_3 k := by decide +kernel
lemma kernel0_0_r2_4_eq : ∀ k : Fin 16, kernel0_0Expr 2 4 k = kernel0_0_r2_4 k := by decide +kernel
lemma kernel0_0_r2_5_eq : ∀ k : Fin 16, kernel0_0Expr 2 5 k = kernel0_0_r2_5 k := by decide +kernel
lemma kernel0_0_r2_6_eq : ∀ k : Fin 16, kernel0_0Expr 2 6 k = kernel0_0_r2_6 k := by decide +kernel
lemma kernel0_0_r2_7_eq : ∀ k : Fin 16, kernel0_0Expr 2 7 k = kernel0_0_r2_7 k := by decide +kernel
lemma kernel0_0_r2_8_eq : ∀ k : Fin 16, kernel0_0Expr 2 8 k = kernel0_0_r2_8 k := by decide +kernel
lemma kernel0_0_r2_9_eq : ∀ k : Fin 16, kernel0_0Expr 2 9 k = kernel0_0_r2_9 k := by decide +kernel
lemma kernel0_0_r2_10_eq : ∀ k : Fin 16, kernel0_0Expr 2 10 k = kernel0_0_r2_10 k := by decide +kernel
lemma kernel0_0_r2_11_eq : ∀ k : Fin 16, kernel0_0Expr 2 11 k = kernel0_0_r2_11 k := by decide +kernel
lemma kernel0_0_r2_12_eq : ∀ k : Fin 16, kernel0_0Expr 2 12 k = kernel0_0_r2_12 k := by decide +kernel
lemma kernel0_0_r2_13_eq : ∀ k : Fin 16, kernel0_0Expr 2 13 k = kernel0_0_r2_13 k := by decide +kernel
lemma kernel0_0_r2_14_eq : ∀ k : Fin 16, kernel0_0Expr 2 14 k = kernel0_0_r2_14 k := by decide +kernel
lemma kernel0_0_r2_15_eq : ∀ k : Fin 16, kernel0_0Expr 2 15 k = kernel0_0_r2_15 k := by decide +kernel
lemma kernel0_0_r2_eq (i k : Fin 16) : kernel0_0Expr 2 i k = kernel0_0_r2 i k := by
  fin_cases i
  · exact kernel0_0_r2_0_eq k
  · exact kernel0_0_r2_1_eq k
  · exact kernel0_0_r2_2_eq k
  · exact kernel0_0_r2_3_eq k
  · exact kernel0_0_r2_4_eq k
  · exact kernel0_0_r2_5_eq k
  · exact kernel0_0_r2_6_eq k
  · exact kernel0_0_r2_7_eq k
  · exact kernel0_0_r2_8_eq k
  · exact kernel0_0_r2_9_eq k
  · exact kernel0_0_r2_10_eq k
  · exact kernel0_0_r2_11_eq k
  · exact kernel0_0_r2_12_eq k
  · exact kernel0_0_r2_13_eq k
  · exact kernel0_0_r2_14_eq k
  · exact kernel0_0_r2_15_eq k
lemma kernel0_0_r3_0_eq : ∀ k : Fin 16, kernel0_0Expr 3 0 k = kernel0_0_r3_0 k := by decide +kernel
lemma kernel0_0_r3_1_eq : ∀ k : Fin 16, kernel0_0Expr 3 1 k = kernel0_0_r3_1 k := by decide +kernel
lemma kernel0_0_r3_2_eq : ∀ k : Fin 16, kernel0_0Expr 3 2 k = kernel0_0_r3_2 k := by decide +kernel
lemma kernel0_0_r3_3_eq : ∀ k : Fin 16, kernel0_0Expr 3 3 k = kernel0_0_r3_3 k := by decide +kernel
lemma kernel0_0_r3_4_eq : ∀ k : Fin 16, kernel0_0Expr 3 4 k = kernel0_0_r3_4 k := by decide +kernel
lemma kernel0_0_r3_5_eq : ∀ k : Fin 16, kernel0_0Expr 3 5 k = kernel0_0_r3_5 k := by decide +kernel
lemma kernel0_0_r3_6_eq : ∀ k : Fin 16, kernel0_0Expr 3 6 k = kernel0_0_r3_6 k := by decide +kernel
lemma kernel0_0_r3_7_eq : ∀ k : Fin 16, kernel0_0Expr 3 7 k = kernel0_0_r3_7 k := by decide +kernel
lemma kernel0_0_r3_8_eq : ∀ k : Fin 16, kernel0_0Expr 3 8 k = kernel0_0_r3_8 k := by decide +kernel
lemma kernel0_0_r3_9_eq : ∀ k : Fin 16, kernel0_0Expr 3 9 k = kernel0_0_r3_9 k := by decide +kernel
lemma kernel0_0_r3_10_eq : ∀ k : Fin 16, kernel0_0Expr 3 10 k = kernel0_0_r3_10 k := by decide +kernel
lemma kernel0_0_r3_11_eq : ∀ k : Fin 16, kernel0_0Expr 3 11 k = kernel0_0_r3_11 k := by decide +kernel
lemma kernel0_0_r3_12_eq : ∀ k : Fin 16, kernel0_0Expr 3 12 k = kernel0_0_r3_12 k := by decide +kernel
lemma kernel0_0_r3_13_eq : ∀ k : Fin 16, kernel0_0Expr 3 13 k = kernel0_0_r3_13 k := by decide +kernel
lemma kernel0_0_r3_14_eq : ∀ k : Fin 16, kernel0_0Expr 3 14 k = kernel0_0_r3_14 k := by decide +kernel
lemma kernel0_0_r3_15_eq : ∀ k : Fin 16, kernel0_0Expr 3 15 k = kernel0_0_r3_15 k := by decide +kernel
lemma kernel0_0_r3_eq (i k : Fin 16) : kernel0_0Expr 3 i k = kernel0_0_r3 i k := by
  fin_cases i
  · exact kernel0_0_r3_0_eq k
  · exact kernel0_0_r3_1_eq k
  · exact kernel0_0_r3_2_eq k
  · exact kernel0_0_r3_3_eq k
  · exact kernel0_0_r3_4_eq k
  · exact kernel0_0_r3_5_eq k
  · exact kernel0_0_r3_6_eq k
  · exact kernel0_0_r3_7_eq k
  · exact kernel0_0_r3_8_eq k
  · exact kernel0_0_r3_9_eq k
  · exact kernel0_0_r3_10_eq k
  · exact kernel0_0_r3_11_eq k
  · exact kernel0_0_r3_12_eq k
  · exact kernel0_0_r3_13_eq k
  · exact kernel0_0_r3_14_eq k
  · exact kernel0_0_r3_15_eq k
lemma kernel0_0_r4_0_eq : ∀ k : Fin 16, kernel0_0Expr 4 0 k = kernel0_0_r4_0 k := by decide +kernel
lemma kernel0_0_r4_1_eq : ∀ k : Fin 16, kernel0_0Expr 4 1 k = kernel0_0_r4_1 k := by decide +kernel
lemma kernel0_0_r4_2_eq : ∀ k : Fin 16, kernel0_0Expr 4 2 k = kernel0_0_r4_2 k := by decide +kernel
lemma kernel0_0_r4_3_eq : ∀ k : Fin 16, kernel0_0Expr 4 3 k = kernel0_0_r4_3 k := by decide +kernel
lemma kernel0_0_r4_4_eq : ∀ k : Fin 16, kernel0_0Expr 4 4 k = kernel0_0_r4_4 k := by decide +kernel
lemma kernel0_0_r4_5_eq : ∀ k : Fin 16, kernel0_0Expr 4 5 k = kernel0_0_r4_5 k := by decide +kernel
lemma kernel0_0_r4_6_eq : ∀ k : Fin 16, kernel0_0Expr 4 6 k = kernel0_0_r4_6 k := by decide +kernel
lemma kernel0_0_r4_7_eq : ∀ k : Fin 16, kernel0_0Expr 4 7 k = kernel0_0_r4_7 k := by decide +kernel
lemma kernel0_0_r4_8_eq : ∀ k : Fin 16, kernel0_0Expr 4 8 k = kernel0_0_r4_8 k := by decide +kernel
lemma kernel0_0_r4_9_eq : ∀ k : Fin 16, kernel0_0Expr 4 9 k = kernel0_0_r4_9 k := by decide +kernel
lemma kernel0_0_r4_10_eq : ∀ k : Fin 16, kernel0_0Expr 4 10 k = kernel0_0_r4_10 k := by decide +kernel
lemma kernel0_0_r4_11_eq : ∀ k : Fin 16, kernel0_0Expr 4 11 k = kernel0_0_r4_11 k := by decide +kernel
lemma kernel0_0_r4_12_eq : ∀ k : Fin 16, kernel0_0Expr 4 12 k = kernel0_0_r4_12 k := by decide +kernel
lemma kernel0_0_r4_13_eq : ∀ k : Fin 16, kernel0_0Expr 4 13 k = kernel0_0_r4_13 k := by decide +kernel
lemma kernel0_0_r4_14_eq : ∀ k : Fin 16, kernel0_0Expr 4 14 k = kernel0_0_r4_14 k := by decide +kernel
lemma kernel0_0_r4_15_eq : ∀ k : Fin 16, kernel0_0Expr 4 15 k = kernel0_0_r4_15 k := by decide +kernel
lemma kernel0_0_r4_eq (i k : Fin 16) : kernel0_0Expr 4 i k = kernel0_0_r4 i k := by
  fin_cases i
  · exact kernel0_0_r4_0_eq k
  · exact kernel0_0_r4_1_eq k
  · exact kernel0_0_r4_2_eq k
  · exact kernel0_0_r4_3_eq k
  · exact kernel0_0_r4_4_eq k
  · exact kernel0_0_r4_5_eq k
  · exact kernel0_0_r4_6_eq k
  · exact kernel0_0_r4_7_eq k
  · exact kernel0_0_r4_8_eq k
  · exact kernel0_0_r4_9_eq k
  · exact kernel0_0_r4_10_eq k
  · exact kernel0_0_r4_11_eq k
  · exact kernel0_0_r4_12_eq k
  · exact kernel0_0_r4_13_eq k
  · exact kernel0_0_r4_14_eq k
  · exact kernel0_0_r4_15_eq k
lemma kernel0_0_r5_0_eq : ∀ k : Fin 16, kernel0_0Expr 5 0 k = kernel0_0_r5_0 k := by decide +kernel
lemma kernel0_0_r5_1_eq : ∀ k : Fin 16, kernel0_0Expr 5 1 k = kernel0_0_r5_1 k := by decide +kernel
lemma kernel0_0_r5_2_eq : ∀ k : Fin 16, kernel0_0Expr 5 2 k = kernel0_0_r5_2 k := by decide +kernel
lemma kernel0_0_r5_3_eq : ∀ k : Fin 16, kernel0_0Expr 5 3 k = kernel0_0_r5_3 k := by decide +kernel
lemma kernel0_0_r5_4_eq : ∀ k : Fin 16, kernel0_0Expr 5 4 k = kernel0_0_r5_4 k := by decide +kernel
lemma kernel0_0_r5_5_eq : ∀ k : Fin 16, kernel0_0Expr 5 5 k = kernel0_0_r5_5 k := by decide +kernel
lemma kernel0_0_r5_6_eq : ∀ k : Fin 16, kernel0_0Expr 5 6 k = kernel0_0_r5_6 k := by decide +kernel
lemma kernel0_0_r5_7_eq : ∀ k : Fin 16, kernel0_0Expr 5 7 k = kernel0_0_r5_7 k := by decide +kernel
lemma kernel0_0_r5_8_eq : ∀ k : Fin 16, kernel0_0Expr 5 8 k = kernel0_0_r5_8 k := by decide +kernel
lemma kernel0_0_r5_9_eq : ∀ k : Fin 16, kernel0_0Expr 5 9 k = kernel0_0_r5_9 k := by decide +kernel
lemma kernel0_0_r5_10_eq : ∀ k : Fin 16, kernel0_0Expr 5 10 k = kernel0_0_r5_10 k := by decide +kernel
lemma kernel0_0_r5_11_eq : ∀ k : Fin 16, kernel0_0Expr 5 11 k = kernel0_0_r5_11 k := by decide +kernel
lemma kernel0_0_r5_12_eq : ∀ k : Fin 16, kernel0_0Expr 5 12 k = kernel0_0_r5_12 k := by decide +kernel
lemma kernel0_0_r5_13_eq : ∀ k : Fin 16, kernel0_0Expr 5 13 k = kernel0_0_r5_13 k := by decide +kernel
lemma kernel0_0_r5_14_eq : ∀ k : Fin 16, kernel0_0Expr 5 14 k = kernel0_0_r5_14 k := by decide +kernel
lemma kernel0_0_r5_15_eq : ∀ k : Fin 16, kernel0_0Expr 5 15 k = kernel0_0_r5_15 k := by decide +kernel
lemma kernel0_0_r5_eq (i k : Fin 16) : kernel0_0Expr 5 i k = kernel0_0_r5 i k := by
  fin_cases i
  · exact kernel0_0_r5_0_eq k
  · exact kernel0_0_r5_1_eq k
  · exact kernel0_0_r5_2_eq k
  · exact kernel0_0_r5_3_eq k
  · exact kernel0_0_r5_4_eq k
  · exact kernel0_0_r5_5_eq k
  · exact kernel0_0_r5_6_eq k
  · exact kernel0_0_r5_7_eq k
  · exact kernel0_0_r5_8_eq k
  · exact kernel0_0_r5_9_eq k
  · exact kernel0_0_r5_10_eq k
  · exact kernel0_0_r5_11_eq k
  · exact kernel0_0_r5_12_eq k
  · exact kernel0_0_r5_13_eq k
  · exact kernel0_0_r5_14_eq k
  · exact kernel0_0_r5_15_eq k
lemma kernel0_0_eq (j : Fin 6) (i k : Fin 16) : kernel0_0Expr j i k = kernel0_0 j i k := by
  fin_cases j
  · exact kernel0_0_r0_eq i k
  · exact kernel0_0_r1_eq i k
  · exact kernel0_0_r2_eq i k
  · exact kernel0_0_r3_eq i k
  · exact kernel0_0_r4_eq i k
  · exact kernel0_0_r5_eq i k
lemma kernel0_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel0_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(0:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel0_0_eq]
  unfold kernel0_0Expr
  have hl := (gridRows_contains_g j i k).2.1
  rw [pointLambda_eq_g] at hl
  have hh := CBox.contains_mul_g hl (trans0_contains j i k)
  simpa only [Bool.false_eq_true,ite_false, if_false,mul_one] using hh
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighFactorBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval bounds for the normalized Gaussian moment powers -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
lemma momentPower_trans_contains {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains ((lambda t*Complex.exp (Complex.I*Real.pi*z t*m))*1))
    (hb : b.Contains (momentPower ell (z t))) :
    (a.mul b).Contains (complexTransformedFactor m 1 ell t) := by
  have hh := CBox.contains_mul_g ha hb
  simpa only [complexTransformedFactor,Complex.ofReal_one,complexLambda_ofReal_g,
    complexZ_ofReal_g,mul_one,momentPower,mul_div_assoc,Complex.ofReal_natCast] using hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian moment bounds at the quadrature nodes and atoms -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
lemma momentPower_trans_full {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains ((lambda t*Complex.exp (Complex.I*Real.pi*z t*m))*1))
    (hb : b.Contains (momentPower ell (z t))) :
    (a.mul b).Contains (fullFactor true m ell t) := by
  simpa only [fullFactor,ite_true, if_true] using momentPower_trans_contains ha hb
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma hk0_1_9_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (hk0_1_9 j i k).Contains (fullFactor true 0 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 9 (kernel0_0_contains j i k) (mpower1_9_contains_g j i k)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hk0_1_9_contains_g_oai := @OAI.SharpPlanar.CachedData.hk0_1_9_contains_g_oai
