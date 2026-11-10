-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm1_1_1_20.contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:52:10.829375+00:00
-- url     : https://prove2.me/submissions/a4689960-45a4-4dcd-bf2d-8f6676528370

import Mathlib
import Definitions.Def_OAIQ098G061
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G984
import Definitions.Def_OAIQ098G996
import Definitions.Def_OAIQ098G1682
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_20_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_trans1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g

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
lemma kernel1_0_r0_0_eq : ∀ k : Fin 16, kernel1_0Expr 0 0 k = kernel1_0_r0_0 k := by decide +kernel
lemma kernel1_0_r0_1_eq : ∀ k : Fin 16, kernel1_0Expr 0 1 k = kernel1_0_r0_1 k := by decide +kernel
lemma kernel1_0_r0_2_eq : ∀ k : Fin 16, kernel1_0Expr 0 2 k = kernel1_0_r0_2 k := by decide +kernel
lemma kernel1_0_r0_3_eq : ∀ k : Fin 16, kernel1_0Expr 0 3 k = kernel1_0_r0_3 k := by decide +kernel
lemma kernel1_0_r0_4_eq : ∀ k : Fin 16, kernel1_0Expr 0 4 k = kernel1_0_r0_4 k := by decide +kernel
lemma kernel1_0_r0_5_eq : ∀ k : Fin 16, kernel1_0Expr 0 5 k = kernel1_0_r0_5 k := by decide +kernel
lemma kernel1_0_r0_6_eq : ∀ k : Fin 16, kernel1_0Expr 0 6 k = kernel1_0_r0_6 k := by decide +kernel
lemma kernel1_0_r0_7_eq : ∀ k : Fin 16, kernel1_0Expr 0 7 k = kernel1_0_r0_7 k := by decide +kernel
lemma kernel1_0_r0_8_eq : ∀ k : Fin 16, kernel1_0Expr 0 8 k = kernel1_0_r0_8 k := by decide +kernel
lemma kernel1_0_r0_9_eq : ∀ k : Fin 16, kernel1_0Expr 0 9 k = kernel1_0_r0_9 k := by decide +kernel
lemma kernel1_0_r0_10_eq : ∀ k : Fin 16, kernel1_0Expr 0 10 k = kernel1_0_r0_10 k := by decide +kernel
lemma kernel1_0_r0_11_eq : ∀ k : Fin 16, kernel1_0Expr 0 11 k = kernel1_0_r0_11 k := by decide +kernel
lemma kernel1_0_r0_12_eq : ∀ k : Fin 16, kernel1_0Expr 0 12 k = kernel1_0_r0_12 k := by decide +kernel
lemma kernel1_0_r0_13_eq : ∀ k : Fin 16, kernel1_0Expr 0 13 k = kernel1_0_r0_13 k := by decide +kernel
lemma kernel1_0_r0_14_eq : ∀ k : Fin 16, kernel1_0Expr 0 14 k = kernel1_0_r0_14 k := by decide +kernel
lemma kernel1_0_r0_15_eq : ∀ k : Fin 16, kernel1_0Expr 0 15 k = kernel1_0_r0_15 k := by decide +kernel
lemma kernel1_0_r0_eq (i k : Fin 16) : kernel1_0Expr 0 i k = kernel1_0_r0 i k := by
  fin_cases i
  · exact kernel1_0_r0_0_eq k
  · exact kernel1_0_r0_1_eq k
  · exact kernel1_0_r0_2_eq k
  · exact kernel1_0_r0_3_eq k
  · exact kernel1_0_r0_4_eq k
  · exact kernel1_0_r0_5_eq k
  · exact kernel1_0_r0_6_eq k
  · exact kernel1_0_r0_7_eq k
  · exact kernel1_0_r0_8_eq k
  · exact kernel1_0_r0_9_eq k
  · exact kernel1_0_r0_10_eq k
  · exact kernel1_0_r0_11_eq k
  · exact kernel1_0_r0_12_eq k
  · exact kernel1_0_r0_13_eq k
  · exact kernel1_0_r0_14_eq k
  · exact kernel1_0_r0_15_eq k
lemma kernel1_0_r1_0_eq : ∀ k : Fin 16, kernel1_0Expr 1 0 k = kernel1_0_r1_0 k := by decide +kernel
lemma kernel1_0_r1_1_eq : ∀ k : Fin 16, kernel1_0Expr 1 1 k = kernel1_0_r1_1 k := by decide +kernel
lemma kernel1_0_r1_2_eq : ∀ k : Fin 16, kernel1_0Expr 1 2 k = kernel1_0_r1_2 k := by decide +kernel
lemma kernel1_0_r1_3_eq : ∀ k : Fin 16, kernel1_0Expr 1 3 k = kernel1_0_r1_3 k := by decide +kernel
lemma kernel1_0_r1_4_eq : ∀ k : Fin 16, kernel1_0Expr 1 4 k = kernel1_0_r1_4 k := by decide +kernel
lemma kernel1_0_r1_5_eq : ∀ k : Fin 16, kernel1_0Expr 1 5 k = kernel1_0_r1_5 k := by decide +kernel
lemma kernel1_0_r1_6_eq : ∀ k : Fin 16, kernel1_0Expr 1 6 k = kernel1_0_r1_6 k := by decide +kernel
lemma kernel1_0_r1_7_eq : ∀ k : Fin 16, kernel1_0Expr 1 7 k = kernel1_0_r1_7 k := by decide +kernel
lemma kernel1_0_r1_8_eq : ∀ k : Fin 16, kernel1_0Expr 1 8 k = kernel1_0_r1_8 k := by decide +kernel
lemma kernel1_0_r1_9_eq : ∀ k : Fin 16, kernel1_0Expr 1 9 k = kernel1_0_r1_9 k := by decide +kernel
lemma kernel1_0_r1_10_eq : ∀ k : Fin 16, kernel1_0Expr 1 10 k = kernel1_0_r1_10 k := by decide +kernel
lemma kernel1_0_r1_11_eq : ∀ k : Fin 16, kernel1_0Expr 1 11 k = kernel1_0_r1_11 k := by decide +kernel
lemma kernel1_0_r1_12_eq : ∀ k : Fin 16, kernel1_0Expr 1 12 k = kernel1_0_r1_12 k := by decide +kernel
lemma kernel1_0_r1_13_eq : ∀ k : Fin 16, kernel1_0Expr 1 13 k = kernel1_0_r1_13 k := by decide +kernel
lemma kernel1_0_r1_14_eq : ∀ k : Fin 16, kernel1_0Expr 1 14 k = kernel1_0_r1_14 k := by decide +kernel
lemma kernel1_0_r1_15_eq : ∀ k : Fin 16, kernel1_0Expr 1 15 k = kernel1_0_r1_15 k := by decide +kernel
lemma kernel1_0_r1_eq (i k : Fin 16) : kernel1_0Expr 1 i k = kernel1_0_r1 i k := by
  fin_cases i
  · exact kernel1_0_r1_0_eq k
  · exact kernel1_0_r1_1_eq k
  · exact kernel1_0_r1_2_eq k
  · exact kernel1_0_r1_3_eq k
  · exact kernel1_0_r1_4_eq k
  · exact kernel1_0_r1_5_eq k
  · exact kernel1_0_r1_6_eq k
  · exact kernel1_0_r1_7_eq k
  · exact kernel1_0_r1_8_eq k
  · exact kernel1_0_r1_9_eq k
  · exact kernel1_0_r1_10_eq k
  · exact kernel1_0_r1_11_eq k
  · exact kernel1_0_r1_12_eq k
  · exact kernel1_0_r1_13_eq k
  · exact kernel1_0_r1_14_eq k
  · exact kernel1_0_r1_15_eq k
lemma kernel1_0_r2_0_eq : ∀ k : Fin 16, kernel1_0Expr 2 0 k = kernel1_0_r2_0 k := by decide +kernel
lemma kernel1_0_r2_1_eq : ∀ k : Fin 16, kernel1_0Expr 2 1 k = kernel1_0_r2_1 k := by decide +kernel
lemma kernel1_0_r2_2_eq : ∀ k : Fin 16, kernel1_0Expr 2 2 k = kernel1_0_r2_2 k := by decide +kernel
lemma kernel1_0_r2_3_eq : ∀ k : Fin 16, kernel1_0Expr 2 3 k = kernel1_0_r2_3 k := by decide +kernel
lemma kernel1_0_r2_4_eq : ∀ k : Fin 16, kernel1_0Expr 2 4 k = kernel1_0_r2_4 k := by decide +kernel
lemma kernel1_0_r2_5_eq : ∀ k : Fin 16, kernel1_0Expr 2 5 k = kernel1_0_r2_5 k := by decide +kernel
lemma kernel1_0_r2_6_eq : ∀ k : Fin 16, kernel1_0Expr 2 6 k = kernel1_0_r2_6 k := by decide +kernel
lemma kernel1_0_r2_7_eq : ∀ k : Fin 16, kernel1_0Expr 2 7 k = kernel1_0_r2_7 k := by decide +kernel
lemma kernel1_0_r2_8_eq : ∀ k : Fin 16, kernel1_0Expr 2 8 k = kernel1_0_r2_8 k := by decide +kernel
lemma kernel1_0_r2_9_eq : ∀ k : Fin 16, kernel1_0Expr 2 9 k = kernel1_0_r2_9 k := by decide +kernel
lemma kernel1_0_r2_10_eq : ∀ k : Fin 16, kernel1_0Expr 2 10 k = kernel1_0_r2_10 k := by decide +kernel
lemma kernel1_0_r2_11_eq : ∀ k : Fin 16, kernel1_0Expr 2 11 k = kernel1_0_r2_11 k := by decide +kernel
lemma kernel1_0_r2_12_eq : ∀ k : Fin 16, kernel1_0Expr 2 12 k = kernel1_0_r2_12 k := by decide +kernel
lemma kernel1_0_r2_13_eq : ∀ k : Fin 16, kernel1_0Expr 2 13 k = kernel1_0_r2_13 k := by decide +kernel
lemma kernel1_0_r2_14_eq : ∀ k : Fin 16, kernel1_0Expr 2 14 k = kernel1_0_r2_14 k := by decide +kernel
lemma kernel1_0_r2_15_eq : ∀ k : Fin 16, kernel1_0Expr 2 15 k = kernel1_0_r2_15 k := by decide +kernel
lemma kernel1_0_r2_eq (i k : Fin 16) : kernel1_0Expr 2 i k = kernel1_0_r2 i k := by
  fin_cases i
  · exact kernel1_0_r2_0_eq k
  · exact kernel1_0_r2_1_eq k
  · exact kernel1_0_r2_2_eq k
  · exact kernel1_0_r2_3_eq k
  · exact kernel1_0_r2_4_eq k
  · exact kernel1_0_r2_5_eq k
  · exact kernel1_0_r2_6_eq k
  · exact kernel1_0_r2_7_eq k
  · exact kernel1_0_r2_8_eq k
  · exact kernel1_0_r2_9_eq k
  · exact kernel1_0_r2_10_eq k
  · exact kernel1_0_r2_11_eq k
  · exact kernel1_0_r2_12_eq k
  · exact kernel1_0_r2_13_eq k
  · exact kernel1_0_r2_14_eq k
  · exact kernel1_0_r2_15_eq k
lemma kernel1_0_r3_0_eq : ∀ k : Fin 16, kernel1_0Expr 3 0 k = kernel1_0_r3_0 k := by decide +kernel
lemma kernel1_0_r3_1_eq : ∀ k : Fin 16, kernel1_0Expr 3 1 k = kernel1_0_r3_1 k := by decide +kernel
lemma kernel1_0_r3_2_eq : ∀ k : Fin 16, kernel1_0Expr 3 2 k = kernel1_0_r3_2 k := by decide +kernel
lemma kernel1_0_r3_3_eq : ∀ k : Fin 16, kernel1_0Expr 3 3 k = kernel1_0_r3_3 k := by decide +kernel
lemma kernel1_0_r3_4_eq : ∀ k : Fin 16, kernel1_0Expr 3 4 k = kernel1_0_r3_4 k := by decide +kernel
lemma kernel1_0_r3_5_eq : ∀ k : Fin 16, kernel1_0Expr 3 5 k = kernel1_0_r3_5 k := by decide +kernel
lemma kernel1_0_r3_6_eq : ∀ k : Fin 16, kernel1_0Expr 3 6 k = kernel1_0_r3_6 k := by decide +kernel
lemma kernel1_0_r3_7_eq : ∀ k : Fin 16, kernel1_0Expr 3 7 k = kernel1_0_r3_7 k := by decide +kernel
lemma kernel1_0_r3_8_eq : ∀ k : Fin 16, kernel1_0Expr 3 8 k = kernel1_0_r3_8 k := by decide +kernel
lemma kernel1_0_r3_9_eq : ∀ k : Fin 16, kernel1_0Expr 3 9 k = kernel1_0_r3_9 k := by decide +kernel
lemma kernel1_0_r3_10_eq : ∀ k : Fin 16, kernel1_0Expr 3 10 k = kernel1_0_r3_10 k := by decide +kernel
lemma kernel1_0_r3_11_eq : ∀ k : Fin 16, kernel1_0Expr 3 11 k = kernel1_0_r3_11 k := by decide +kernel
lemma kernel1_0_r3_12_eq : ∀ k : Fin 16, kernel1_0Expr 3 12 k = kernel1_0_r3_12 k := by decide +kernel
lemma kernel1_0_r3_13_eq : ∀ k : Fin 16, kernel1_0Expr 3 13 k = kernel1_0_r3_13 k := by decide +kernel
lemma kernel1_0_r3_14_eq : ∀ k : Fin 16, kernel1_0Expr 3 14 k = kernel1_0_r3_14 k := by decide +kernel
lemma kernel1_0_r3_15_eq : ∀ k : Fin 16, kernel1_0Expr 3 15 k = kernel1_0_r3_15 k := by decide +kernel
lemma kernel1_0_r3_eq (i k : Fin 16) : kernel1_0Expr 3 i k = kernel1_0_r3 i k := by
  fin_cases i
  · exact kernel1_0_r3_0_eq k
  · exact kernel1_0_r3_1_eq k
  · exact kernel1_0_r3_2_eq k
  · exact kernel1_0_r3_3_eq k
  · exact kernel1_0_r3_4_eq k
  · exact kernel1_0_r3_5_eq k
  · exact kernel1_0_r3_6_eq k
  · exact kernel1_0_r3_7_eq k
  · exact kernel1_0_r3_8_eq k
  · exact kernel1_0_r3_9_eq k
  · exact kernel1_0_r3_10_eq k
  · exact kernel1_0_r3_11_eq k
  · exact kernel1_0_r3_12_eq k
  · exact kernel1_0_r3_13_eq k
  · exact kernel1_0_r3_14_eq k
  · exact kernel1_0_r3_15_eq k
lemma kernel1_0_r4_0_eq : ∀ k : Fin 16, kernel1_0Expr 4 0 k = kernel1_0_r4_0 k := by decide +kernel
lemma kernel1_0_r4_1_eq : ∀ k : Fin 16, kernel1_0Expr 4 1 k = kernel1_0_r4_1 k := by decide +kernel
lemma kernel1_0_r4_2_eq : ∀ k : Fin 16, kernel1_0Expr 4 2 k = kernel1_0_r4_2 k := by decide +kernel
lemma kernel1_0_r4_3_eq : ∀ k : Fin 16, kernel1_0Expr 4 3 k = kernel1_0_r4_3 k := by decide +kernel
lemma kernel1_0_r4_4_eq : ∀ k : Fin 16, kernel1_0Expr 4 4 k = kernel1_0_r4_4 k := by decide +kernel
lemma kernel1_0_r4_5_eq : ∀ k : Fin 16, kernel1_0Expr 4 5 k = kernel1_0_r4_5 k := by decide +kernel
lemma kernel1_0_r4_6_eq : ∀ k : Fin 16, kernel1_0Expr 4 6 k = kernel1_0_r4_6 k := by decide +kernel
lemma kernel1_0_r4_7_eq : ∀ k : Fin 16, kernel1_0Expr 4 7 k = kernel1_0_r4_7 k := by decide +kernel
lemma kernel1_0_r4_8_eq : ∀ k : Fin 16, kernel1_0Expr 4 8 k = kernel1_0_r4_8 k := by decide +kernel
lemma kernel1_0_r4_9_eq : ∀ k : Fin 16, kernel1_0Expr 4 9 k = kernel1_0_r4_9 k := by decide +kernel
lemma kernel1_0_r4_10_eq : ∀ k : Fin 16, kernel1_0Expr 4 10 k = kernel1_0_r4_10 k := by decide +kernel
lemma kernel1_0_r4_11_eq : ∀ k : Fin 16, kernel1_0Expr 4 11 k = kernel1_0_r4_11 k := by decide +kernel
lemma kernel1_0_r4_12_eq : ∀ k : Fin 16, kernel1_0Expr 4 12 k = kernel1_0_r4_12 k := by decide +kernel
lemma kernel1_0_r4_13_eq : ∀ k : Fin 16, kernel1_0Expr 4 13 k = kernel1_0_r4_13 k := by decide +kernel
lemma kernel1_0_r4_14_eq : ∀ k : Fin 16, kernel1_0Expr 4 14 k = kernel1_0_r4_14 k := by decide +kernel
lemma kernel1_0_r4_15_eq : ∀ k : Fin 16, kernel1_0Expr 4 15 k = kernel1_0_r4_15 k := by decide +kernel
lemma kernel1_0_r4_eq (i k : Fin 16) : kernel1_0Expr 4 i k = kernel1_0_r4 i k := by
  fin_cases i
  · exact kernel1_0_r4_0_eq k
  · exact kernel1_0_r4_1_eq k
  · exact kernel1_0_r4_2_eq k
  · exact kernel1_0_r4_3_eq k
  · exact kernel1_0_r4_4_eq k
  · exact kernel1_0_r4_5_eq k
  · exact kernel1_0_r4_6_eq k
  · exact kernel1_0_r4_7_eq k
  · exact kernel1_0_r4_8_eq k
  · exact kernel1_0_r4_9_eq k
  · exact kernel1_0_r4_10_eq k
  · exact kernel1_0_r4_11_eq k
  · exact kernel1_0_r4_12_eq k
  · exact kernel1_0_r4_13_eq k
  · exact kernel1_0_r4_14_eq k
  · exact kernel1_0_r4_15_eq k
lemma kernel1_0_r5_0_eq : ∀ k : Fin 16, kernel1_0Expr 5 0 k = kernel1_0_r5_0 k := by decide +kernel
lemma kernel1_0_r5_1_eq : ∀ k : Fin 16, kernel1_0Expr 5 1 k = kernel1_0_r5_1 k := by decide +kernel
lemma kernel1_0_r5_2_eq : ∀ k : Fin 16, kernel1_0Expr 5 2 k = kernel1_0_r5_2 k := by decide +kernel
lemma kernel1_0_r5_3_eq : ∀ k : Fin 16, kernel1_0Expr 5 3 k = kernel1_0_r5_3 k := by decide +kernel
lemma kernel1_0_r5_4_eq : ∀ k : Fin 16, kernel1_0Expr 5 4 k = kernel1_0_r5_4 k := by decide +kernel
lemma kernel1_0_r5_5_eq : ∀ k : Fin 16, kernel1_0Expr 5 5 k = kernel1_0_r5_5 k := by decide +kernel
lemma kernel1_0_r5_6_eq : ∀ k : Fin 16, kernel1_0Expr 5 6 k = kernel1_0_r5_6 k := by decide +kernel
lemma kernel1_0_r5_7_eq : ∀ k : Fin 16, kernel1_0Expr 5 7 k = kernel1_0_r5_7 k := by decide +kernel
lemma kernel1_0_r5_8_eq : ∀ k : Fin 16, kernel1_0Expr 5 8 k = kernel1_0_r5_8 k := by decide +kernel
lemma kernel1_0_r5_9_eq : ∀ k : Fin 16, kernel1_0Expr 5 9 k = kernel1_0_r5_9 k := by decide +kernel
lemma kernel1_0_r5_10_eq : ∀ k : Fin 16, kernel1_0Expr 5 10 k = kernel1_0_r5_10 k := by decide +kernel
lemma kernel1_0_r5_11_eq : ∀ k : Fin 16, kernel1_0Expr 5 11 k = kernel1_0_r5_11 k := by decide +kernel
lemma kernel1_0_r5_12_eq : ∀ k : Fin 16, kernel1_0Expr 5 12 k = kernel1_0_r5_12 k := by decide +kernel
lemma kernel1_0_r5_13_eq : ∀ k : Fin 16, kernel1_0Expr 5 13 k = kernel1_0_r5_13 k := by decide +kernel
lemma kernel1_0_r5_14_eq : ∀ k : Fin 16, kernel1_0Expr 5 14 k = kernel1_0_r5_14 k := by decide +kernel
lemma kernel1_0_r5_15_eq : ∀ k : Fin 16, kernel1_0Expr 5 15 k = kernel1_0_r5_15 k := by decide +kernel
lemma kernel1_0_r5_eq (i k : Fin 16) : kernel1_0Expr 5 i k = kernel1_0_r5 i k := by
  fin_cases i
  · exact kernel1_0_r5_0_eq k
  · exact kernel1_0_r5_1_eq k
  · exact kernel1_0_r5_2_eq k
  · exact kernel1_0_r5_3_eq k
  · exact kernel1_0_r5_4_eq k
  · exact kernel1_0_r5_5_eq k
  · exact kernel1_0_r5_6_eq k
  · exact kernel1_0_r5_7_eq k
  · exact kernel1_0_r5_8_eq k
  · exact kernel1_0_r5_9_eq k
  · exact kernel1_0_r5_10_eq k
  · exact kernel1_0_r5_11_eq k
  · exact kernel1_0_r5_12_eq k
  · exact kernel1_0_r5_13_eq k
  · exact kernel1_0_r5_14_eq k
  · exact kernel1_0_r5_15_eq k
lemma kernel1_0_eq (j : Fin 6) (i k : Fin 16) : kernel1_0Expr j i k = kernel1_0 j i k := by
  fin_cases j
  · exact kernel1_0_r0_eq i k
  · exact kernel1_0_r1_eq i k
  · exact kernel1_0_r2_eq i k
  · exact kernel1_0_r3_eq i k
  · exact kernel1_0_r4_eq i k
  · exact kernel1_0_r5_eq i k
lemma kernel1_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel1_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(1:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel1_0_eq]
  unfold kernel1_0Expr
  have hl := (gridRows_contains_g j i k).2.1
  rw [pointLambda_eq_g] at hl
  have hh := CBox.contains_mul_g hl (trans1_contains_g j i k)
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders1
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
lemma hk1_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_20 j i k).Contains (fullFactor true 1 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 20 (kernel1_0_contains j i k) (mpower1_20_contains_g j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_6
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
namespace hm1_1_1_20
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox density1 hk1_1_20 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains_g_oai : ans.Contains (fullMomentRule true true 1 20) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density1 hk1_1_20 (tableDensity true) (fullFactor true 1 20) density1_contains_g hk1_1_20_contains
end hm1_1_1_20
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm1_1_1_20.contains_g_oai := @OAI.SharpPlanar.CachedData.hm1_1_1_20.contains_g_oai
