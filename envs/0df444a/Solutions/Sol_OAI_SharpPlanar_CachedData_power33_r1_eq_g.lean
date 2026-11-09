-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.power33_r1_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:16:43.101772+00:00
-- url     : https://prove2.me/submissions/5e8d6d0f-12f2-41a9-a44b-2ea3a980676c

import Mathlib
import Definitions.Def_OAIQ098G250
import Definitions.Def_OAIQ098G319

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
lemma power33_r1_0_eq : ∀ k : Fin 16, power33Expr 1 0 k = power33_r1_0 k := by decide +kernel
lemma power33_r1_1_eq : ∀ k : Fin 16, power33Expr 1 1 k = power33_r1_1 k := by decide +kernel
lemma power33_r1_2_eq : ∀ k : Fin 16, power33Expr 1 2 k = power33_r1_2 k := by decide +kernel
lemma power33_r1_3_eq : ∀ k : Fin 16, power33Expr 1 3 k = power33_r1_3 k := by decide +kernel
lemma power33_r1_4_eq : ∀ k : Fin 16, power33Expr 1 4 k = power33_r1_4 k := by decide +kernel
lemma power33_r1_5_eq : ∀ k : Fin 16, power33Expr 1 5 k = power33_r1_5 k := by decide +kernel
lemma power33_r1_6_eq : ∀ k : Fin 16, power33Expr 1 6 k = power33_r1_6 k := by decide +kernel
lemma power33_r1_7_eq : ∀ k : Fin 16, power33Expr 1 7 k = power33_r1_7 k := by decide +kernel
lemma power33_r1_8_eq : ∀ k : Fin 16, power33Expr 1 8 k = power33_r1_8 k := by decide +kernel
lemma power33_r1_9_eq : ∀ k : Fin 16, power33Expr 1 9 k = power33_r1_9 k := by decide +kernel
lemma power33_r1_10_eq : ∀ k : Fin 16, power33Expr 1 10 k = power33_r1_10 k := by decide +kernel
lemma power33_r1_11_eq : ∀ k : Fin 16, power33Expr 1 11 k = power33_r1_11 k := by decide +kernel
lemma power33_r1_12_eq : ∀ k : Fin 16, power33Expr 1 12 k = power33_r1_12 k := by decide +kernel
lemma power33_r1_13_eq : ∀ k : Fin 16, power33Expr 1 13 k = power33_r1_13 k := by decide +kernel
lemma power33_r1_14_eq : ∀ k : Fin 16, power33Expr 1 14 k = power33_r1_14 k := by decide +kernel
lemma power33_r1_15_eq : ∀ k : Fin 16, power33Expr 1 15 k = power33_r1_15 k := by decide +kernel
lemma power33_r1_eq_g_oai (i k : Fin 16) : power33Expr 1 i k = power33_r1 i k := by
  fin_cases i
  · exact power33_r1_0_eq k
  · exact power33_r1_1_eq k
  · exact power33_r1_2_eq k
  · exact power33_r1_3_eq k
  · exact power33_r1_4_eq k
  · exact power33_r1_5_eq k
  · exact power33_r1_6_eq k
  · exact power33_r1_7_eq k
  · exact power33_r1_8_eq k
  · exact power33_r1_9_eq k
  · exact power33_r1_10_eq k
  · exact power33_r1_11_eq k
  · exact power33_r1_12_eq k
  · exact power33_r1_13_eq k
  · exact power33_r1_14_eq k
  · exact power33_r1_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.power33_r1_eq_g_oai := @OAI.SharpPlanar.CachedData.power33_r1_eq_g_oai
