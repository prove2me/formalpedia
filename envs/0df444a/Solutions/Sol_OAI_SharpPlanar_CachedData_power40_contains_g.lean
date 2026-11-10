-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power40_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:17:26.654984+00:00
-- url     : https://prove2.me/submissions/af7d6f38-adca-414e-b5da-a1a9d382dd72

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G259
import Definitions.Def_OAIQ098G322
import Theorems.Thm_OAI_SharpPlanar_CachedData_power38_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power39_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power40_r1_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
lemma power39_contains (j : Fin 6) (i k : Fin 16) :
    (power39 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(39:ℕ))) := by
  rw [← power39_eq_g]
  unfold power39Expr
  convert exp_direct_step_g (power38_contains_g j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power40_r0_0_eq : ∀ k : Fin 16, power40Expr 0 0 k = power40_r0_0 k := by decide +kernel
lemma power40_r0_1_eq : ∀ k : Fin 16, power40Expr 0 1 k = power40_r0_1 k := by decide +kernel
lemma power40_r0_2_eq : ∀ k : Fin 16, power40Expr 0 2 k = power40_r0_2 k := by decide +kernel
lemma power40_r0_3_eq : ∀ k : Fin 16, power40Expr 0 3 k = power40_r0_3 k := by decide +kernel
lemma power40_r0_4_eq : ∀ k : Fin 16, power40Expr 0 4 k = power40_r0_4 k := by decide +kernel
lemma power40_r0_5_eq : ∀ k : Fin 16, power40Expr 0 5 k = power40_r0_5 k := by decide +kernel
lemma power40_r0_6_eq : ∀ k : Fin 16, power40Expr 0 6 k = power40_r0_6 k := by decide +kernel
lemma power40_r0_7_eq : ∀ k : Fin 16, power40Expr 0 7 k = power40_r0_7 k := by decide +kernel
lemma power40_r0_8_eq : ∀ k : Fin 16, power40Expr 0 8 k = power40_r0_8 k := by decide +kernel
lemma power40_r0_9_eq : ∀ k : Fin 16, power40Expr 0 9 k = power40_r0_9 k := by decide +kernel
lemma power40_r0_10_eq : ∀ k : Fin 16, power40Expr 0 10 k = power40_r0_10 k := by decide +kernel
lemma power40_r0_11_eq : ∀ k : Fin 16, power40Expr 0 11 k = power40_r0_11 k := by decide +kernel
lemma power40_r0_12_eq : ∀ k : Fin 16, power40Expr 0 12 k = power40_r0_12 k := by decide +kernel
lemma power40_r0_13_eq : ∀ k : Fin 16, power40Expr 0 13 k = power40_r0_13 k := by decide +kernel
lemma power40_r0_14_eq : ∀ k : Fin 16, power40Expr 0 14 k = power40_r0_14 k := by decide +kernel
lemma power40_r0_15_eq : ∀ k : Fin 16, power40Expr 0 15 k = power40_r0_15 k := by decide +kernel
lemma power40_r0_eq (i k : Fin 16) : power40Expr 0 i k = power40_r0 i k := by
  fin_cases i
  · exact power40_r0_0_eq k
  · exact power40_r0_1_eq k
  · exact power40_r0_2_eq k
  · exact power40_r0_3_eq k
  · exact power40_r0_4_eq k
  · exact power40_r0_5_eq k
  · exact power40_r0_6_eq k
  · exact power40_r0_7_eq k
  · exact power40_r0_8_eq k
  · exact power40_r0_9_eq k
  · exact power40_r0_10_eq k
  · exact power40_r0_11_eq k
  · exact power40_r0_12_eq k
  · exact power40_r0_13_eq k
  · exact power40_r0_14_eq k
  · exact power40_r0_15_eq k
lemma power40_r2_0_eq : ∀ k : Fin 16, power40Expr 2 0 k = power40_r2_0 k := by decide +kernel
lemma power40_r2_1_eq : ∀ k : Fin 16, power40Expr 2 1 k = power40_r2_1 k := by decide +kernel
lemma power40_r2_2_eq : ∀ k : Fin 16, power40Expr 2 2 k = power40_r2_2 k := by decide +kernel
lemma power40_r2_3_eq : ∀ k : Fin 16, power40Expr 2 3 k = power40_r2_3 k := by decide +kernel
lemma power40_r2_4_eq : ∀ k : Fin 16, power40Expr 2 4 k = power40_r2_4 k := by decide +kernel
lemma power40_r2_5_eq : ∀ k : Fin 16, power40Expr 2 5 k = power40_r2_5 k := by decide +kernel
lemma power40_r2_6_eq : ∀ k : Fin 16, power40Expr 2 6 k = power40_r2_6 k := by decide +kernel
lemma power40_r2_7_eq : ∀ k : Fin 16, power40Expr 2 7 k = power40_r2_7 k := by decide +kernel
lemma power40_r2_8_eq : ∀ k : Fin 16, power40Expr 2 8 k = power40_r2_8 k := by decide +kernel
lemma power40_r2_9_eq : ∀ k : Fin 16, power40Expr 2 9 k = power40_r2_9 k := by decide +kernel
lemma power40_r2_10_eq : ∀ k : Fin 16, power40Expr 2 10 k = power40_r2_10 k := by decide +kernel
lemma power40_r2_11_eq : ∀ k : Fin 16, power40Expr 2 11 k = power40_r2_11 k := by decide +kernel
lemma power40_r2_12_eq : ∀ k : Fin 16, power40Expr 2 12 k = power40_r2_12 k := by decide +kernel
lemma power40_r2_13_eq : ∀ k : Fin 16, power40Expr 2 13 k = power40_r2_13 k := by decide +kernel
lemma power40_r2_14_eq : ∀ k : Fin 16, power40Expr 2 14 k = power40_r2_14 k := by decide +kernel
lemma power40_r2_15_eq : ∀ k : Fin 16, power40Expr 2 15 k = power40_r2_15 k := by decide +kernel
lemma power40_r2_eq (i k : Fin 16) : power40Expr 2 i k = power40_r2 i k := by
  fin_cases i
  · exact power40_r2_0_eq k
  · exact power40_r2_1_eq k
  · exact power40_r2_2_eq k
  · exact power40_r2_3_eq k
  · exact power40_r2_4_eq k
  · exact power40_r2_5_eq k
  · exact power40_r2_6_eq k
  · exact power40_r2_7_eq k
  · exact power40_r2_8_eq k
  · exact power40_r2_9_eq k
  · exact power40_r2_10_eq k
  · exact power40_r2_11_eq k
  · exact power40_r2_12_eq k
  · exact power40_r2_13_eq k
  · exact power40_r2_14_eq k
  · exact power40_r2_15_eq k
lemma power40_r3_0_eq : ∀ k : Fin 16, power40Expr 3 0 k = power40_r3_0 k := by decide +kernel
lemma power40_r3_1_eq : ∀ k : Fin 16, power40Expr 3 1 k = power40_r3_1 k := by decide +kernel
lemma power40_r3_2_eq : ∀ k : Fin 16, power40Expr 3 2 k = power40_r3_2 k := by decide +kernel
lemma power40_r3_3_eq : ∀ k : Fin 16, power40Expr 3 3 k = power40_r3_3 k := by decide +kernel
lemma power40_r3_4_eq : ∀ k : Fin 16, power40Expr 3 4 k = power40_r3_4 k := by decide +kernel
lemma power40_r3_5_eq : ∀ k : Fin 16, power40Expr 3 5 k = power40_r3_5 k := by decide +kernel
lemma power40_r3_6_eq : ∀ k : Fin 16, power40Expr 3 6 k = power40_r3_6 k := by decide +kernel
lemma power40_r3_7_eq : ∀ k : Fin 16, power40Expr 3 7 k = power40_r3_7 k := by decide +kernel
lemma power40_r3_8_eq : ∀ k : Fin 16, power40Expr 3 8 k = power40_r3_8 k := by decide +kernel
lemma power40_r3_9_eq : ∀ k : Fin 16, power40Expr 3 9 k = power40_r3_9 k := by decide +kernel
lemma power40_r3_10_eq : ∀ k : Fin 16, power40Expr 3 10 k = power40_r3_10 k := by decide +kernel
lemma power40_r3_11_eq : ∀ k : Fin 16, power40Expr 3 11 k = power40_r3_11 k := by decide +kernel
lemma power40_r3_12_eq : ∀ k : Fin 16, power40Expr 3 12 k = power40_r3_12 k := by decide +kernel
lemma power40_r3_13_eq : ∀ k : Fin 16, power40Expr 3 13 k = power40_r3_13 k := by decide +kernel
lemma power40_r3_14_eq : ∀ k : Fin 16, power40Expr 3 14 k = power40_r3_14 k := by decide +kernel
lemma power40_r3_15_eq : ∀ k : Fin 16, power40Expr 3 15 k = power40_r3_15 k := by decide +kernel
lemma power40_r3_eq (i k : Fin 16) : power40Expr 3 i k = power40_r3 i k := by
  fin_cases i
  · exact power40_r3_0_eq k
  · exact power40_r3_1_eq k
  · exact power40_r3_2_eq k
  · exact power40_r3_3_eq k
  · exact power40_r3_4_eq k
  · exact power40_r3_5_eq k
  · exact power40_r3_6_eq k
  · exact power40_r3_7_eq k
  · exact power40_r3_8_eq k
  · exact power40_r3_9_eq k
  · exact power40_r3_10_eq k
  · exact power40_r3_11_eq k
  · exact power40_r3_12_eq k
  · exact power40_r3_13_eq k
  · exact power40_r3_14_eq k
  · exact power40_r3_15_eq k
lemma power40_r4_0_eq : ∀ k : Fin 16, power40Expr 4 0 k = power40_r4_0 k := by decide +kernel
lemma power40_r4_1_eq : ∀ k : Fin 16, power40Expr 4 1 k = power40_r4_1 k := by decide +kernel
lemma power40_r4_2_eq : ∀ k : Fin 16, power40Expr 4 2 k = power40_r4_2 k := by decide +kernel
lemma power40_r4_3_eq : ∀ k : Fin 16, power40Expr 4 3 k = power40_r4_3 k := by decide +kernel
lemma power40_r4_4_eq : ∀ k : Fin 16, power40Expr 4 4 k = power40_r4_4 k := by decide +kernel
lemma power40_r4_5_eq : ∀ k : Fin 16, power40Expr 4 5 k = power40_r4_5 k := by decide +kernel
lemma power40_r4_6_eq : ∀ k : Fin 16, power40Expr 4 6 k = power40_r4_6 k := by decide +kernel
lemma power40_r4_7_eq : ∀ k : Fin 16, power40Expr 4 7 k = power40_r4_7 k := by decide +kernel
lemma power40_r4_8_eq : ∀ k : Fin 16, power40Expr 4 8 k = power40_r4_8 k := by decide +kernel
lemma power40_r4_9_eq : ∀ k : Fin 16, power40Expr 4 9 k = power40_r4_9 k := by decide +kernel
lemma power40_r4_10_eq : ∀ k : Fin 16, power40Expr 4 10 k = power40_r4_10 k := by decide +kernel
lemma power40_r4_11_eq : ∀ k : Fin 16, power40Expr 4 11 k = power40_r4_11 k := by decide +kernel
lemma power40_r4_12_eq : ∀ k : Fin 16, power40Expr 4 12 k = power40_r4_12 k := by decide +kernel
lemma power40_r4_13_eq : ∀ k : Fin 16, power40Expr 4 13 k = power40_r4_13 k := by decide +kernel
lemma power40_r4_14_eq : ∀ k : Fin 16, power40Expr 4 14 k = power40_r4_14 k := by decide +kernel
lemma power40_r4_15_eq : ∀ k : Fin 16, power40Expr 4 15 k = power40_r4_15 k := by decide +kernel
lemma power40_r4_eq (i k : Fin 16) : power40Expr 4 i k = power40_r4 i k := by
  fin_cases i
  · exact power40_r4_0_eq k
  · exact power40_r4_1_eq k
  · exact power40_r4_2_eq k
  · exact power40_r4_3_eq k
  · exact power40_r4_4_eq k
  · exact power40_r4_5_eq k
  · exact power40_r4_6_eq k
  · exact power40_r4_7_eq k
  · exact power40_r4_8_eq k
  · exact power40_r4_9_eq k
  · exact power40_r4_10_eq k
  · exact power40_r4_11_eq k
  · exact power40_r4_12_eq k
  · exact power40_r4_13_eq k
  · exact power40_r4_14_eq k
  · exact power40_r4_15_eq k
lemma power40_r5_0_eq : ∀ k : Fin 16, power40Expr 5 0 k = power40_r5_0 k := by decide +kernel
lemma power40_r5_1_eq : ∀ k : Fin 16, power40Expr 5 1 k = power40_r5_1 k := by decide +kernel
lemma power40_r5_2_eq : ∀ k : Fin 16, power40Expr 5 2 k = power40_r5_2 k := by decide +kernel
lemma power40_r5_3_eq : ∀ k : Fin 16, power40Expr 5 3 k = power40_r5_3 k := by decide +kernel
lemma power40_r5_4_eq : ∀ k : Fin 16, power40Expr 5 4 k = power40_r5_4 k := by decide +kernel
lemma power40_r5_5_eq : ∀ k : Fin 16, power40Expr 5 5 k = power40_r5_5 k := by decide +kernel
lemma power40_r5_6_eq : ∀ k : Fin 16, power40Expr 5 6 k = power40_r5_6 k := by decide +kernel
lemma power40_r5_7_eq : ∀ k : Fin 16, power40Expr 5 7 k = power40_r5_7 k := by decide +kernel
lemma power40_r5_8_eq : ∀ k : Fin 16, power40Expr 5 8 k = power40_r5_8 k := by decide +kernel
lemma power40_r5_9_eq : ∀ k : Fin 16, power40Expr 5 9 k = power40_r5_9 k := by decide +kernel
lemma power40_r5_10_eq : ∀ k : Fin 16, power40Expr 5 10 k = power40_r5_10 k := by decide +kernel
lemma power40_r5_11_eq : ∀ k : Fin 16, power40Expr 5 11 k = power40_r5_11 k := by decide +kernel
lemma power40_r5_12_eq : ∀ k : Fin 16, power40Expr 5 12 k = power40_r5_12 k := by decide +kernel
lemma power40_r5_13_eq : ∀ k : Fin 16, power40Expr 5 13 k = power40_r5_13 k := by decide +kernel
lemma power40_r5_14_eq : ∀ k : Fin 16, power40Expr 5 14 k = power40_r5_14 k := by decide +kernel
lemma power40_r5_15_eq : ∀ k : Fin 16, power40Expr 5 15 k = power40_r5_15 k := by decide +kernel
lemma power40_r5_eq (i k : Fin 16) : power40Expr 5 i k = power40_r5 i k := by
  fin_cases i
  · exact power40_r5_0_eq k
  · exact power40_r5_1_eq k
  · exact power40_r5_2_eq k
  · exact power40_r5_3_eq k
  · exact power40_r5_4_eq k
  · exact power40_r5_5_eq k
  · exact power40_r5_6_eq k
  · exact power40_r5_7_eq k
  · exact power40_r5_8_eq k
  · exact power40_r5_9_eq k
  · exact power40_r5_10_eq k
  · exact power40_r5_11_eq k
  · exact power40_r5_12_eq k
  · exact power40_r5_13_eq k
  · exact power40_r5_14_eq k
  · exact power40_r5_15_eq k
lemma power40_eq (j : Fin 6) (i k : Fin 16) : power40Expr j i k = power40 j i k := by
  fin_cases j
  · exact power40_r0_eq i k
  · exact power40_r1_eq_g i k
  · exact power40_r2_eq i k
  · exact power40_r3_eq i k
  · exact power40_r4_eq i k
  · exact power40_r5_eq i k
lemma power40_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (power40 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(40:ℕ))) := by
  rw [← power40_eq]
  unfold power40Expr
  convert exp_direct_step_g (power39_contains j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power40_contains_g_oai := @OAI.SharpPlanar.CachedData.power40_contains_g_oai
