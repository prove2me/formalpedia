-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power31_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:46:43.428004+00:00
-- url     : https://prove2.me/submissions/56104a29-103d-46f0-aeac-853e644a4c55

import Mathlib
import Definitions.Def_OAIQ098G251
import Definitions.Def_OAIQ098G319
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r5_eq_g

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
lemma power31_r3_0_eq : ∀ k : Fin 16, power31Expr 3 0 k = power31_r3_0 k := by decide +kernel
lemma power31_r3_1_eq : ∀ k : Fin 16, power31Expr 3 1 k = power31_r3_1 k := by decide +kernel
lemma power31_r3_2_eq : ∀ k : Fin 16, power31Expr 3 2 k = power31_r3_2 k := by decide +kernel
lemma power31_r3_3_eq : ∀ k : Fin 16, power31Expr 3 3 k = power31_r3_3 k := by decide +kernel
lemma power31_r3_4_eq : ∀ k : Fin 16, power31Expr 3 4 k = power31_r3_4 k := by decide +kernel
lemma power31_r3_5_eq : ∀ k : Fin 16, power31Expr 3 5 k = power31_r3_5 k := by decide +kernel
lemma power31_r3_6_eq : ∀ k : Fin 16, power31Expr 3 6 k = power31_r3_6 k := by decide +kernel
lemma power31_r3_7_eq : ∀ k : Fin 16, power31Expr 3 7 k = power31_r3_7 k := by decide +kernel
lemma power31_r3_8_eq : ∀ k : Fin 16, power31Expr 3 8 k = power31_r3_8 k := by decide +kernel
lemma power31_r3_9_eq : ∀ k : Fin 16, power31Expr 3 9 k = power31_r3_9 k := by decide +kernel
lemma power31_r3_10_eq : ∀ k : Fin 16, power31Expr 3 10 k = power31_r3_10 k := by decide +kernel
lemma power31_r3_11_eq : ∀ k : Fin 16, power31Expr 3 11 k = power31_r3_11 k := by decide +kernel
lemma power31_r3_12_eq : ∀ k : Fin 16, power31Expr 3 12 k = power31_r3_12 k := by decide +kernel
lemma power31_r3_13_eq : ∀ k : Fin 16, power31Expr 3 13 k = power31_r3_13 k := by decide +kernel
lemma power31_r3_14_eq : ∀ k : Fin 16, power31Expr 3 14 k = power31_r3_14 k := by decide +kernel
lemma power31_r3_15_eq : ∀ k : Fin 16, power31Expr 3 15 k = power31_r3_15 k := by decide +kernel
lemma power31_r3_eq (i k : Fin 16) : power31Expr 3 i k = power31_r3 i k := by
  fin_cases i
  · exact power31_r3_0_eq k
  · exact power31_r3_1_eq k
  · exact power31_r3_2_eq k
  · exact power31_r3_3_eq k
  · exact power31_r3_4_eq k
  · exact power31_r3_5_eq k
  · exact power31_r3_6_eq k
  · exact power31_r3_7_eq k
  · exact power31_r3_8_eq k
  · exact power31_r3_9_eq k
  · exact power31_r3_10_eq k
  · exact power31_r3_11_eq k
  · exact power31_r3_12_eq k
  · exact power31_r3_13_eq k
  · exact power31_r3_14_eq k
  · exact power31_r3_15_eq k
lemma power31_eq_g_oai (j : Fin 6) (i k : Fin 16) : power31Expr j i k = power31 j i k := by
  fin_cases j
  · exact power31_r0_eq_g i k
  · exact power31_r1_eq_g i k
  · exact power31_r2_eq_g i k
  · exact power31_r3_eq i k
  · exact power31_r4_eq_g i k
  · exact power31_r5_eq_g i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power31_eq_g_oai := @OAI.SharpPlanar.CachedData.power31_eq_g_oai
